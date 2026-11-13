-- Prove2me | Theorems.Thm_BosonicLearn_isDensity_prod
-- name    : BosonicLearn.isDensity_prod
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T05:28:58.447374+00:00
-- url     : https://prove2.me/theorems/9ba77185-dcd9-40fb-a0fa-53b6f03019b3
-- title:
--   The tensor product $X\otimes Y$ of two density operators is a density operator
-- statement:
--   The tensor product of two density operators is a density operator.
--
--   Let $A$ and $B$ be index sets, $X$ a density operator on $\ell^2(A)$ and $Y$ a density operator on $\ell^2(B)$, given by their matrices. Then the matrix
--
--   $$
--   (X\otimes Y)\big((a,b),(a',b')\big)=X(a,a')\,Y(b,b')
--   $$
--
--   is a density operator on $\ell^2(A\times B)$: it is trace class, its finite quadratic forms are real and non-negative, and its diagonal is summable with sum $1$.
--
--   Role. Product states of several copies, in particular $\rho^{\otimes N}$, are density operators of the multi-copy system, so that the Born rule of a collective POVM applies to them.
--
--   **Formalization Note** Density operators are `IsDensity` of `Dependency50.P33`, with trace class meaning the existence of a nuclear expansion $\sum_k|\ell_k\rangle\langle r_k|$ with $\sum_k\|\ell_k\|\|r_k\|<\infty$. The index sets are arbitrary.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators), `BosonicLearn.effect_trace_pairing` (Born sums along nuclear expansions), `BosonicLearn.fockPOVM_form_measure` (effects are weakly $\sigma$-additive) and `BosonicLearn.fockPOVM_postprocess`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1, p. 4, Figure 1 ("many i.i.d. copies of an unknown quantum state"); the N-copy state ρ^{⊗N} of Theorem 3, pp. 6–7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

namespace BosonicLearn

/-- **The tensor product of two density operators is a density operator.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1, p. 4, Figure 1: "An experimental device … generates many i.i.d. copies of an unknown quantum state of
interest"; the `N`-copy state `ρ^{⊗N}` is used throughout (e.g. Theorem 3, pp. 6–7).

If `X` is a density operator on `ℓ²(A)` and `Y` a density operator on `ℓ²(B)`, then `X ⊗ Y`, with entries
`X(a, a') Y(b, b')` at `((a, b), (a', b'))`, is a density operator on `ℓ²(A × B)`.

**Formalization Note.** Density operators are `IsDensity` of `Dependency50.P33`: trace class in the
nuclear-expansion sense, non-negative real finite quadratic forms, and summable diagonal with sum one. The index
sets are arbitrary. -/
theorem isDensity_prod {A B : Type} {X : Matrix A A ℂ} {Y : Matrix B B ℂ}
    (hX : IsDensity X) (hY : IsDensity Y) :
    IsDensity (fun p q : A × B => X p.1 q.1 * Y p.2 q.2) := by sorry

end BosonicLearn
