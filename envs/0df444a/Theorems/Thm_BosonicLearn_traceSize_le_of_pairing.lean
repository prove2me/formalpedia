-- Prove2me | Theorems.Thm_BosonicLearn_traceSize_le_of_pairing
-- name    : BosonicLearn.traceSize_le_of_pairing
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:24:46.857295+00:00
-- url     : https://prove2.me/theorems/fa27c047-0217-4be1-be23-09cf26a497e3
-- title:
--   Trace norm by duality: if $|\mathrm{Tr}(AV)|\le c$ for all contractions $V$ then $\|A\|_1\le c$ (self-adjoint $A$ on $\ell^2(I)$)
-- statement:
--   The variational characterization of the trace norm, in the direction needed to *bound* it, for the nuclear-expansion definition `traceSize`.
--
--   Let $A$ be a bounded self-adjoint operator on $\ell^2(I)$ ($I$ countable) and $c\ge0$. If for every operator $V$ with $\|V\|\le1$ and every finite set $F$ of basis indices
--
--   $$\Big|\sum_{u\in F}\langle e_u,AVe_u\rangle\Big|\le c,$$
--
--   then the matrix $(\langle e_u,Ae_v\rangle)_{u,v}$ is trace class with trace norm at most $c$.
--
--   Proof idea: with the continuous functional calculus, $A=A_+-A_-$ and $|A|=A_++A_-$; the contractions $V_\varepsilon=A(|A|+\varepsilon)^{-1}$ give $\sum_{u\in F}\langle e_u,|A|e_u\rangle\le c+\varepsilon|F|$, so $\operatorname{Tr}A_++\operatorname{Tr}A_-\le c$, and a positive operator with finite trace $t$ has a nuclear expansion of total weight $t$.
--
--   **Formalization Note** `traceSize` is the infimum over nuclear expansions ($\infty$ if there is none), so the conclusion includes that $A$ is trace class. $e_u$ is `lp.single 2 u 1` in `Hilbert I`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, footnote 1, p. 3 (trace distance $\frac12\|\rho-\sigma\|_1$); §7.1, p. 55 (trace-distance bounds between Gaussian states)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.RealRegisters (Hilbert)
open scoped ENNReal

namespace BosonicLearn

/-- **Trace norm by duality: `‖A‖₁ ≤ sup_{‖V‖ ≤ 1} |Tr(AV)|` for self-adjoint `A`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, footnote 1, p. 3 (trace distance `½‖ρ − σ‖₁`), and §7.1, p. 55 (trace-distance bounds between Gaussian states); this is the
standard variational characterization of the trace norm used to bound it.

Let `A` be a bounded self-adjoint operator on `ℓ²(I)` and `c ≥ 0`. If for every contraction `V` and every finite set
`F` of basis indices the partial trace `∑_{u ∈ F} ⟨e_u, A V e_u⟩` has modulus at most `c`, then the matrix of `A` in
the standard basis is trace class with trace norm at most `c`.

**Formalization Note.** `traceSize` is the infimum over nuclear expansions (`∞` if there is none), so the conclusion
includes that `A` is trace class. The matrix of `A` is `⟨e_u, A e_v⟩`, `e_u = lp.single 2 u 1`. -/
theorem traceSize_le_of_pairing {I : Type} [DecidableEq I] [Countable I] (A : Hilbert I →L[ℂ] Hilbert I)
    (hA : IsSelfAdjoint A) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ V : Hilbert I →L[ℂ] Hilbert I, ‖V‖ ≤ 1 → ∀ F : Finset I,
      ‖∑ u ∈ F, inner ℂ (lp.single 2 u (1 : ℂ) : Hilbert I) (A (V (lp.single 2 u (1 : ℂ))))‖ ≤ c) :
    traceSize (fun u v : I => inner ℂ (lp.single 2 u (1 : ℂ) : Hilbert I) (A (lp.single 2 v (1 : ℂ)))) ≤
      ENNReal.ofReal c := by sorry

end BosonicLearn
