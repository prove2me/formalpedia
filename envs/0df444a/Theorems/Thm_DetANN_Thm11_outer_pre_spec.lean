-- Prove2me | Theorems.Thm_DetANN_Thm11_outer_pre_spec
-- name    : DetANN.Thm11.outer_pre_spec
-- status  : Open
-- author  : @milia
-- created : 2026-11-23T21:58:35.206177+00:00
-- url     : https://prove2.me/theorems/b17ae3a4-2130-4e55-9326-dced196506ea
-- title:
--   Theorem 1.1, outer preprocessing: time, space, and the stored state
-- statement:
--   Let $\mathrm{Pre}_3,\mathrm{Qry}_3$ be deterministic programs that satisfy $\mathrm{InnerSpec}(\mathrm{Pre}_3,\mathrm{Qry}_3,C,K,C_p)$ (definition `DetANN_Thm11_Stored`, the guarantees of Lemma 3.3) with $C>1$, and let $C_b\ge C$ be an integer. Let the inner program that this half of the outer structure runs ($\mathrm{Pre}_3$ for preprocessing, $\mathrm{Qry}_3$ for queries) use only registers below $n_3$ (`UsesBelow`) and have integer literals of absolute value at most $X_3\ge1$ (`LitBound`). Write $\mathrm{outerPre}$ and $\mathrm{outerQry}$ for the programs of definition `DetANN_Thm11_OuterProg` with these parameters and a literal $c_0$.
--
--   Then there is $c_0^{\min}$ such that for every $c_0\ge c_0^{\min}$ there are constants $C_m,K_m$ with the following property. For every instance with $n\ge2$, $1\le d\le n$, injective $P:[n]\to\mathbb R^d$ and $\varepsilon\in(0,1)$, there are $t$, a padding exponent $k$ and a constant $C_0\ge c_0$ such that:
--   - $\mathrm{outerPre}$ started on the input layout of $P$ with parameter $\varepsilon$ has halted after $t$ steps;
--   - its work and the number of cells it stored to are both at most
--   $$C_m\,n^{K_m\varepsilon^{-K_m}};$$
--   - the halted state satisfies $\mathrm{OuterStored}(\mathrm{Pre}_3,X_3,\mathrm{innerQT},P,\varepsilon,C_0,k)$ (definition `DetANN_Thm11_Stored`).
--
--   This is the preprocessing half of the machine part of Theorem 1.1 (theorem `outer_composition`). The bound reflects the inner preprocessing time $(C/\delta)^{Km}$ with $m=16^\ell L$ and $L=O(\varepsilon^{-4}\log n)$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' for the machine part of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split
import Definitions.Def_DetANN_Thm11_OuterProg
import Definitions.Def_DetANN_Thm11_Stored

namespace DetANN

namespace Thm11

open PNormReg PNormRegLib

/-- **The outer preprocessing (P).** For an inner pair with the guarantees of Lemma 3.3 (register
bound `n3` and literal bound `X3`, constants `C ≤ Cb`, `K`, `Cp`) there is a threshold `c0min`
such that for every literal `c0 ≥ c0min` there are constants `Cm, Km` with: for every instance with
`n ≥ 2`, the outer preprocessing halts within `Cm·n^{Km ε^{−Km}}` steps, stores to at most that
many cells, and its halted state is `OuterStored` for some padding `k` and some `C₀ ≥ c0`. -/
theorem outer_pre_spec :
    ∀ (Pre₃ Qry₃ : Program), DetProgram Pre₃ → DetProgram Qry₃ →
      ∀ (n3 X3 : ℕ), UsesBelow Pre₃ n3 n3 → LitBound Pre₃ X3 → 1 ≤ X3 →
        ∀ (C : ℝ) (K Cp Cb : ℕ), 1 < C → C ≤ Cb → InnerSpec Pre₃ Qry₃ C K Cp →
          ∃ c0min : ℕ, ∀ c0 : ℕ, c0min ≤ c0 → ∃ Cm Km : ℕ, ∀ d n : ℕ, 1 ≤ d → d ≤ n → 2 ≤ n →
            ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
              ∀ ε : ℝ, 0 < ε → ε < 1 →
                ∃ (t k : ℕ) (C₀ : ℝ), (c0 : ℝ) ≤ C₀ ∧
                  (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).halted = true ∧
                  ((run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).work : ℝ) ≤
                    (Cm : ℝ) * (n : ℝ) ^ ((Km : ℝ) * ε⁻¹ ^ Km) ∧
                  ((cellsWritten (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) t).card : ℝ) ≤
                    (Cm : ℝ) * (n : ℝ) ^ ((Km : ℝ) * ε⁻¹ ^ Km) ∧
                  OuterStored Pre₃ X3 (innerQT Cp C₀ k P ε) P ε C₀ k
                    (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) := by
  sorry

end Thm11

end DetANN
