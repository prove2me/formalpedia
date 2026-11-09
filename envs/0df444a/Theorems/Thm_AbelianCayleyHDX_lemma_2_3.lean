-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_2_3
-- name    : AbelianCayleyHDX.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:58.228363+00:00
-- url     : https://prove2.me/theorems/7105dca6-243e-4bd0-b0e2-63ac49b424b2
-- title:
--   Lemma 2.3 — explicit relation matrices with $\dim\ker H \ge 2h\,2^{t/3}$ and $\|P_H|_{\mathbf 1^\perp}\| \le \lambda$
-- statement:
--   For every fixed $\lambda > 0$ and every $q = 2^h \ge 8$ with $3/(q-2) \le \lambda$: for arbitrarily large integers $t$ one can explicitly construct a binary matrix $H \in \mathbb F_2^{R \times M}$, where $M = (q^2-1)q^{2t}$, $R = \rho M/3$ and $\rho = O_\lambda(t)$, such that
--   1. the rows are distinct and have weight three, every column has weight $\rho > 0$, and $\mathrm{rowspan}_{\mathbb F_2} H$ has minimum distance at least three;
--   2. writing $n = \dim_{\mathbb F_2}\ker H$,
--   $$n \ge 2h\, 2^{t/3}; \qquad (2.2)$$
--   3. the operator $P_H$ of (2.1) is the normalized adjacency operator of a connected simple regular graph and $\|P_H|_{\mathbf 1^\perp}\| \le \lambda$.
--
--   Precisely: there are a constant $C$, a sequence $t_j \to \infty$ and matrices $H_j$ (with $R_j$ rows, $M_j = (q^2-1)q^{2t_j}$ columns, column weight $\rho_j \le C t_j$) with these properties, and one Turing machine and one polynomial $p$ such that the machine, given $j$ in binary, outputs $R_j$, $M_j$ and the rows of $H_j$ within $p(M_j)$ steps.
--
--   Differences from the source:
--   - reading: choose $q = 2^h \ge 8$ with $3/(q-2) \le \lambda$ → every $h$ with $8 \le 2^h$ and $3/(2^h - 2) \le \lambda$; reason: the lemma holds for whichever admissible $q$ is chosen; its proof (Section 3.3) uses only these two conditions
--   - reading: for arbitrarily large integers $t$ one can explicitly construct $H$ → a sequence $t_j \to \infty$ and one machine producing $H_j$ from $j$ within time polynomial in $M_j$; reason: Section 3.3, p.14: rows "can be enumerated … in time polynomial in the output size"
--   - reading: $\rho = O_\lambda(t)$ → $\rho_j \le C t_j$, $C$ chosen after $\lambda$ and $h$; reason: the $O_\lambda$ constant may depend on $\lambda$ and on the chosen $q$
--   - encoding: $H \in \mathbb F_2^{R \times M}$ with $R = \rho M/3$ → `Matrix (Fin R) (Fin M) (ZMod 2)` with $3R = \rho M$; output as its rows of $M$ bits; reason: avoids natural-number division
--   - encoding: normalized adjacency of a connected simple regular graph; $\|P_H|_{\mathbf 1^\perp}\| \le \lambda$ → a connected `SimpleGraph` regular of degree $d$ with $P_H = A/d$; $\|P_H f\|_2 \le \lambda\|f\|_2$ for $\sum f = 0$; reason: for a regular graph the stationary measure is uniform (p.8)
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.3, p.10, Eq. (2.2)

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_PH
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
open Filter RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX

open Classical in
/-- **Lemma 2.3** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.3, p.10, Eq. (2.2)). For every fixed `λ > 0` and `q = 2^h ≥ 8`
with `3/(q − 2) ≤ λ`, for arbitrarily large integers `t` one can explicitly construct a binary
matrix `H ∈ 𝔽₂^{R × M}`, `M = (q² − 1) q^{2t}`, `R = ρM/3`, `ρ = O_λ(t)`, such that
1. the rows are distinct and have weight three, every column has weight `ρ > 0`, and
   `rowspan_{𝔽₂} H` has minimum distance at least three;
2. `n = dim_{𝔽₂} ker H ≥ 2h · 2^{t/3}`;
3. `P_H` of (2.1) is the normalized adjacency operator of a connected simple regular graph and
   `‖P_H|_{1^⊥}‖ ≤ λ`.

Stated as: a constant `C` (depending on `λ` and `q`), a sequence `t_j → ∞`, and matrices `H_j`
with these properties and `ρ_j ≤ C t_j`; and one Turing machine and one polynomial `p` such that
the machine, given `j` in binary, outputs `R_j`, `M_j` and the rows of `H_j` within `p(M_j)` steps.

**Formalization Note** Columns are `Fin M`, rows `Fin R`; a row is output as its `M` bits.
"Explicitly construct" is read as time polynomial in `M` (the output size; Section 3.3, p.14: "in
time polynomial in the output size"). The graph is regular (of some degree `d`) and `P_H = A/d`;
the norm on `1^⊥` is the plain Euclidean norm (the graph is regular, p.8). -/
theorem lemma_2_3 (lam : ℝ) (hlam : 0 < lam) (h : ℕ) (hq : 8 ≤ 2 ^ h)
    (hqlam : 3 / ((2 : ℝ) ^ h - 2) ≤ lam) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧
      ∃ (R ρ : ℕ → ℕ) (H : ∀ j, Matrix (Fin (R j)) (Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) (ZMod 2)),
        (∀ j, 3 * R j = ρ j * (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) ∧ (ρ j : ℝ) ≤ C * (t j : ℝ) ∧
          IsGoodRelationMatrix (H j) (ρ j) ∧
          2 * (h : ℝ) * (2 : ℝ) ^ ((t j : ℝ) / 3) ≤ (Module.finrank (ZMod 2) (kerF2 (H j)) : ℝ) ∧
          ∃ G : SimpleGraph (Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))), G.Connected ∧
            ∃ d : ℕ, G.IsRegularOfDegree d ∧ PH (H j) (ρ j) = (1 / (d : ℝ)) • G.adjMatrix ℝ ∧
            ∀ f : Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) → ℝ, ∑ i, f i = 0 →
              Real.sqrt (∑ i, ((PH (H j) (ρ j)).mulVec f i) ^ 2) ≤ lam * Real.sqrt (∑ i, f i ^ 2)) ∧
        ∃ Mach : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial ℕ, ∀ j,
          HMBinPacking.OutputsWithin Mach (encNat j)
            (encNat (R j) ++ encNat (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) ++ encList encVec (List.ofFn (H j)))
            (p.eval (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) := by sorry

end AbelianCayleyHDX
