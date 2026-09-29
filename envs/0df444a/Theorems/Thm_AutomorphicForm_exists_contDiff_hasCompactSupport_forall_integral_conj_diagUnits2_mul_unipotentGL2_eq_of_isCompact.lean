-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_conj_diagUnits2_mul_unipotentGL2_eq_of_isCompact
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_forall_integral_conj_diagUnits2_mul_unipotentGL2_eq_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/c76d155f-c515-5bca-aed8-05db1a0f97cc
-- title:
--   Smooth compactly supported descent of archimedean orbital averages
-- statement:
--   Let $K$ be a number field and let $fa : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$, where $K_\infty$ denotes the infinite adele ring of $K$, be an archimedean test factor in the sense of [`AutomorphicForm.IsArchTestFactor`](def/AutomorphicForm_FactorizableTestFn.html#L27): there is a map $\Phi$ on $2\times 2$ arrays of elements of the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $K$ which is $C^\infty$ over $\mathbb{R}$ and satisfies $fa(g)=\Phi(\mathrm{archEntries}(g))$, the entries of $g$ transported through the ring isomorphism `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace`, and moreover $fa$ has compact support. Let $\mathbf{K}_\infty$ be the subgroup $\bigsqcap_w$ of $\mathrm{GL}_2(K_\infty)$ obtained as the infimum, over the infinite places $w$ of $K$, of the preimages under the component map $\mathrm{GL}_2(K_\infty)\to\mathrm{GL}_2(K_w)$ of the row-isometry subgroups, i.e. of those $k$ whose determinant has absolute value $1$ and for which $(x,y)\mapsto (x k_{00}+y k_{10},\ x k_{01}+y k_{11})$ preserves $\lVert x\rVert^2+\lVert y\rVert^2$; let $\kappa$ be a Haar measure on $\mathbf{K}_\infty$ for its Borel $\sigma$-algebra. Then there exists $\Psi$ on triples of elements of the mixed space of $K$, indexed by `Fin 3`, which is $C^\infty$ over $\mathbb{R}$ and compactly supported, such that (i) there is a compact set $Ca \subseteq K_\infty^\times\times K_\infty^\times$ with the property that every $p$ in the topological support of $\Psi$ has its $0$-th and $1$-st coordinates equal to the images in the mixed space of the two components of some $q \in Ca$, and (ii) for all units $a,t \in K_\infty^\times$ and all $x \in K_\infty$, $$\int_{\mathbf{K}_\infty} fa\bigl(k^{-1}\,\mathrm{diag}(a,at)\,\begin{pmatrix}1&x\\0&1\end{pmatrix}\,k\bigr)\,d\kappa(k) = \Psi(\iota t,\ \iota a,\ \iota x),$$ where $\iota$ is the mixed-space isomorphism and the diagonal and unipotent matrices are `diagUnits2 a (a*t)` and [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17).
--
--   This is the archimedean smoothness-and-support input for the Harish-Chandra style descent: averaging an archimedean test factor by conjugation over the archimedean maximal compact produces a smooth compactly supported function of the torus and unipotent parameters $(t,a,x)$, with the first two coordinates of its support confined to a compact set of units. It is used in the derivation of the weighted orbital-integral identity [`AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex), where the resulting $\Psi$ serves as the smooth density to be analysed place by place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_conj_diagUnits2_mul_unipotentGL2_eq_of_isCompact.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_forall_integral_conj_diagUnits2_mul_unipotentGL2_eq_of_isCompact
    (K : Type) [Field K] [NumberField K]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (κ : @Measure (↥(⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ Ψ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ) (x : InfiniteAdeleRing K),
        @integral _ ℂ _ _ (borel _) κ (fun k =>
            fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ * (diagUnits2 a (a * t) * AutomorphicForm.unipotentGL2 x) *
              (k : GL (Fin 2) (InfiniteAdeleRing K)))) =
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] := by sorry
