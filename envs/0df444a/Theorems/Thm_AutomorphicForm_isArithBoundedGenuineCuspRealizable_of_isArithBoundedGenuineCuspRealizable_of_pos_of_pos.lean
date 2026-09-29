-- Prove2me | Theorems.Thm_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
-- name    : AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/237fc9da-54d1-5b00-83e3-191608cb7574
-- title:
--   Transporting arithmetic bounded genuine cusp-realizability to Siegel windows
-- statement:
--   Let $K$ be a number field, let $D$ be an arbitrary set of points of $\mathrm{GL}_2$ over the adeles of $K$, let $U$ assign to every ideal of $\mathcal{O}_K$ a subgroup of that adelic group, let $\mathrm{gen}$ assign to every finite place of $K$ such a point, and let $B$ be a set of adeles; let $\Phi$ be a complex Hecke eigensystem for $K$, that is, a nonzero level ideal of $\mathcal{O}_K$ together with two families $a,b$ of complex numbers indexed by the finite places. Assume that the predicate `IsArithBoundedGenuineCuspRealizable` holds for $\Phi$ relative to the standard additive character `StandardAddChar.stdAddChar K` of the adeles, at the production pins `productionPinsOf K D U gen B` (Borel structure and Haar measure on the adelic $\mathrm{GL}_2$, domain $D$, full centre subgroup, the given $U$ and $\mathrm{gen}$, Borel structure on the adeles and the adelic additive Haar measure conditioned on $B$); unfolded, this says that the raw central rescaling of $\Phi$ — same level and same $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$ — admits a smooth cusp realization at those pins which is a bounded genuine cusp realization for that character. Then, for all real numbers $c,u,d_1,d_2$ with $c>0$ and $d_1>0$ and every finite set $T$ of adelic $\mathrm{GL}_2$ points, the same predicate holds for $\Phi$, relative to the same character and with the same $U$, $\mathrm{gen}$ and $B$, at the production pins whose domain is $\bigcup_{x\in T}\,\mathfrak{S}(c,u,d_1,d_2)\,x$, the union of the right translates by the elements of $T$ of the centre-cut Siegel set consisting of those $g$ whose finite part is integral and whose archimedean component satisfies, at every infinite place, $\mathrm{localHeight}\ge c$, $\mathrm{xWindowSq}\le u^2$ and determinant norm in $[d_1,d_2]$.
--
--   This is the transport step which replaces the integration domain pinned down in the carrier data by a Siegel window with a positive height floor and a positive lower determinant bound, leaving the realization of the eigensystem itself untouched. It is used in the construction of an arithmetic bounded genuine cusp realization descending through `galRestrict`, namely by [`AutomorphicForm.exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict`](thm.html#AutomorphicForm.exists_isArithBoundedGenuineCuspRealizable_eq_comap_galRestrict).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos.lean

import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithBoundedGenuineCuspRealizable_of_pos_of_pos
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithBoundedGenuineCuspRealizable K (productionPinsOf K D U gen B)
      (StandardAddChar.stdAddChar K) Φ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsArithBoundedGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B)
      (StandardAddChar.stdAddChar K) Φ := by sorry
