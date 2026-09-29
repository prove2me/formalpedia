-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact_chain
-- name    : AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact_chain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/2de2250c-d984-59df-8815-8ceddbf2af3c
-- title:
--   Finiteness of fppf cohomology along a finite chain
-- statement:
--   Let $S$ be a scheme and $k, n$ natural numbers. Consider a family $F : \mathrm{Fin}(k+1) \to$ (abelian sheaves on the small fppf site of $S$), where the site is the small Grothendieck topology on the category `S.Fppf` of $S$-schemes whose structure morphism is flat and locally of finite presentation, and the sheaves take values in abelian groups one universe up; together with morphisms $\mathrm{incl}_i : F(i.\mathrm{castSucc}) \to F(i.\mathrm{succ})$ for each $i : \mathrm{Fin}\,k$, forming a chain $F(0) \to F(1) \to \cdots \to F(k)$. Write $H^n_{\mathrm{fppf}}(S,\mathcal F)$ for the $n$-th sheaf cohomology group `fppfCohomology S F n`, defined as the derived-functor cohomology $\mathcal F.H\,n$ of the sheaf on this site. Assume that $H^n_{\mathrm{fppf}}(S, F(0))$ is a finite type, and that for each $i : \mathrm{Fin}\,k$ there exist an abelian sheaf $L$ on the same site and a morphism $\pi : F(i.\mathrm{succ}) \to L$ with $\mathrm{incl}_i$ followed by $\pi$ equal to zero, such that the resulting short complex $F(i.\mathrm{castSucc}) \to F(i.\mathrm{succ}) \to L$ is short exact (that is, $\mathrm{incl}_i$ is a monomorphism, $\pi$ an epimorphism, and the complex exact in the middle) and $H^n_{\mathrm{fppf}}(S, L)$ is finite. The conclusion is that $H^n_{\mathrm{fppf}}(S, F(\mathrm{Fin.last}\,k))$ is finite.
--
--   This is the dévissage step for finiteness of fppf cohomology: finiteness propagates from the bottom of a finite filtration to its top provided each successive quotient layer has finite cohomology in the same degree. It is invoked in the analysis of the primary torsion of the Néron model attached to the $j = 0$ situation on the modular curve, where the layers of a Jordan–Hölder type flag are elementary group schemes whose $H^1$ is controlled directly. Note that the layers are supplied existentially rather than as categorical cokernels, so a consumer may use any sheaf fitting into a short exact sequence with the given inclusion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact_chain.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact_chain
    (S : Scheme.{u}) {k : ℕ} (F : Fin (k + 1) → Sheaf (smallFppfTopology S) Ab.{u + 1})
    (incl : ∀ i : Fin k, F i.castSucc ⟶ F i.succ) (n : ℕ)
    (h0 : Finite (fppfCohomology S (F 0) n))
    (hL : ∀ i : Fin k, ∃ (L : Sheaf (smallFppfTopology S) Ab.{u + 1}) (π : F i.succ ⟶ L)
      (w : incl i ≫ π = 0), (ShortComplex.mk (incl i) π w).ShortExact ∧
        Finite (fppfCohomology S L n)) :
    Finite (fppfCohomology S (F (Fin.last k)) n) := by sorry
