-- Prove2me | Theorems.Thm_DetANN_Thm11_outer_composition
-- name    : DetANN.Thm11.outer_composition
-- status  : Open
-- author  : @milia
-- created : 2026-11-21T08:47:02.732261+00:00
-- url     : https://prove2.me/theorems/862b3c59-19d8-444b-aee6-56c6453bd536
-- title:
--   The composed data structure of §7.4: the machine part of Theorem 1.1
-- statement:
--   Let $\mathrm{Pre}_3,\mathrm{Qry}_3$ be deterministic programs, and let $C>1$ and $K,C'\in\mathbb N$ be such that the pair has the guarantees of Lemma 3.3. That is, for all $m,N\ge1$, every injective $Y:[N]\to\mathbb R^m$ and every $\delta\in(0,1/2)$, it is a deterministic $(1+\delta)$-ANN structure for $Y$ with:
--   - preprocessing time $C'(N+m)^K(C/\delta)^{Km}\log^K(N/\delta)$;
--   - space $C'N(C/\delta)^{Km}\log^K(N/\delta)$;
--   - query time $C'm^2\log^2(N/\delta)$.
--
--   Let $C_0^s>0$. Then there are deterministic programs $\mathrm{Pre},\mathrm{Qry}$ and constants $C_m,K_m\in\mathbb N$ with the following property. For every instance ($1\le d\le n$, injective $P:[n]\to\mathbb R^d$, $\varepsilon\in(0,1)$) there are $k$ with $d\le2^k$ and $C_0\ge C_0^s$ such that:
--   - preprocessing (input parameter $\varepsilon$) halts within $C_m\,n^{K_m\varepsilon^{-K_m}}$ steps and stores to at most that many cells;
--   - every query $q\in\mathbb R^d$ is answered within $C_m\big(d^2+d\,\varepsilon^{-K_m}(1+\log n)^{K_m}\big)$ steps;
--   - every answer $a$ satisfies $\mathrm{LocalAnswer}(C_0,k,P,\varepsilon,q,a)$ (definition `DetANN_Thm11_Split`). That is, some candidates $x_v$, one per walk tuple $v$, satisfy the local guarantee (25) with $\alpha=1+\varepsilon/100$ for the blocks $\mathrm{annBlocks}\,C_0\,k\,P\,\varepsilon$ and the tuples $\mathrm{annTuples}\,k\,\varepsilon$, and $\|q-P_a\|\le\|q-P_{x_v}\|$ for all $v$.
--
--   This is the construction of §7.4. Pad to $\mathbb R^{2^k}$ and build the greedy blocks of Theorem 3.2 with $\tau=\varepsilon^2/10^6$. For each $v$, preprocess the superblock projections $\mathcal A_vP$ (dimension $16^\ell L$) with a relocated copy of $\mathrm{Pre}_3$ in its own memory window. A query runs a relocated $\mathrm{Qry}_3$ in each window and returns the best of the $2^k$ candidates.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as the top-level reduction of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split

namespace DetANN

namespace Thm11

/-- **The composed data structure of §7.4 (machine part of Theorem 1.1).** Given any deterministic
pair `Pre₃, Qry₃` with the guarantees of Lemma 3.3 (constants `C > 1`, `K`, `C'`) and any `C₀s > 0`,
there are deterministic outer programs and constants `Cm, Km` such that for every instance
(`1 ≤ d ≤ n`, injective `P`, `ε ∈ (0, 1)`) there are a padding exponent `k` with `d ≤ 2^k` and a
`C₀ ≥ C₀s` for which preprocessing halts within `Cm·n^{Km·ε^{−Km}}` steps and stores to at most
that many cells, and every query is answered within `Cm·(d² + d·ε^{−Km}(1 + log n)^{Km})` steps by
an index that is at least as close to `q` as some family of candidates satisfying the local
guarantee (25) with `α = 1 + ε/100` for `annBlocks C₀ k P ε` and `annTuples k ε`. -/
theorem outer_composition :
    ∀ (Pre₃ Qry₃ : PNormReg.Program), DetProgram Pre₃ → DetProgram Qry₃ →
      ∀ (C : ℝ) (K C' : ℕ), 1 < C →
        (∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
          ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
            ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
              IsDetANNStructure Pre₃ Qry₃ Y δ (1 + δ)
                ((C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
                ((C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
                ((C' : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2)) →
        ∀ C₀s : ℝ, 0 < C₀s →
          ∃ Pre Qry : PNormReg.Program, DetProgram Pre ∧ DetProgram Qry ∧
            ∃ Cm Km : ℕ, ∀ d n : ℕ, 1 ≤ d → d ≤ n →
              ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
                ∀ ε : ℝ, 0 < ε → ε < 1 →
                  ∃ (k : ℕ) (C₀ : ℝ), d ≤ 2 ^ k ∧ C₀s ≤ C₀ ∧
                    IsDetStructure Pre Qry P ε (LocalAnswer C₀ k P ε)
                      ((Cm : ℝ) * (n : ℝ) ^ ((Km : ℝ) * ε⁻¹ ^ Km))
                      ((Cm : ℝ) * (n : ℝ) ^ ((Km : ℝ) * ε⁻¹ ^ Km))
                      ((Cm : ℝ) * ((d : ℝ) ^ 2 + d * ε⁻¹ ^ Km * (1 + Real.log n) ^ Km)) := by sorry

end Thm11

end DetANN
