-- Prove2me | Theorems.Thm_BoltzmannContinuation_global_extension
-- name    : BoltzmannContinuation.global_extension
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-07T18:37:34.177954+00:00
-- url     : https://prove2.me/theorems/46c164f5-d763-4043-8feb-439a5fa9a2f4
-- title:
--   Global entropy-admissible continuation of a finite solution segment
-- statement:
--   Let $f_0$ be an initial density and let $F$ be an entropy-admissible evolution for the periodic hard-sphere Boltzmann equation on $[0,T]$, where $T>0$. Assume strong $L^1$ continuity and separate space-time integrability of the unrenormalized gain and loss on that interval. Then there exists a global entropy-admissible evolution $G$ with initial datum $f_0$ such that
--
--   $$G(t)=F(t)\quad\text{a.e. on phase space for every }t\in[0,T].$$
--
--   The global evolution retains the supplied early strong continuity and collision integrability. Finite-interval admissibility includes finite entropy at every time, weak continuity, uniform entropy moments, collision-fiber integrability, separate renormalized collision integrability, terminal-trace weak renormalized and local-mass identities, total momentum conservation, and every-time energy and entropy-dissipation inequalities. The conclusion imposes all of the target definition of global admissibility. This continuation interface is independent of the particular nonuniqueness construction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/build/sections/06-admissibility.tex; Section 6, subsection “Continuation and inherited bounds”, concatenation at time T using the periodic DiPerna–Lions theorem. See also Levermore–Masmoudi 2010, Section 4.1, Theorem 4.1, https://doi.org/10.1007/s00205-009-0254-5.

import Definitions.Def_BoltzmannFiniteInterval

noncomputable section
open MeasureTheory Set Filter
open OAI.BoltzmannNonuniqueness

namespace BoltzmannContinuation

/-- Extend a finite entropy-admissible segment without changing its time sections.
The strong regularity remains confined to the supplied early interval. -/
theorem global_extension (f₀ : Density) (F : Evolution) (T : ℝ)
    (hF : AdmissibleOn f₀ T F) (hstrong : StrongEarly T F) :
    ∃ G : Evolution, AdmissibleGlobal f₀ G ∧ StrongEarly T G ∧
      ∀ t ∈ Set.Icc 0 T, G t =ᵐ[volume] F t := by sorry

end BoltzmannContinuation
