-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv
-- name    : FiniteEnergyPlane.hadamard_integral_fderiv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T11:03:27.533154+00:00
-- url     : https://prove2.me/theorems/1de4fd53-940b-44d7-9b66-70ca76fa30c1
-- title:
--   Hadamard's lemma with parameters
-- statement:
--   Let $X,E,F$ be real normed spaces with $F$ complete, and let $f:X\times E\to F$ be $C^\infty$. Put $$g(x,a)=\int_0^1 D_2f(x,\theta a)\,d\theta\in L(E,F),$$ where $D_2f$ is the derivative in the second variable. Then $g$ is $C^\infty$ and $$f(x,a)=f(x,0)+g(x,a)\,a$$ for all $(x,a)\in X\times E$.
--
--   It writes a smooth family of maps that vanish at $a=0$ as a smooth family of linear maps applied to $a$, with the coefficient at $a=0$ equal to $D_2f(x,0)$.
--
--   **Formalization Note** $D_2f(x,\cdot)$ is `fderiv ℝ (fun a => f (x, a))`, and $g$ is written out as an interval integral of continuous linear maps.
-- source:
--   Standard (Hadamard's lemma with parameters); e.g. J. Milnor, Morse Theory, Lemma 2.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Let `f : X × E → F` be `C^∞`. Then `g(x, a) = ∫₀¹ D₂f(x, θa) dθ` is `C^∞` and
`f(x, a) = f(x, 0) + g(x, a) a` for all `(x, a)`. -/
theorem hadamard_integral_fderiv {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : X × E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : X × E => ∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => f (p.1, a)) (θ • p.2)) ∧
      ∀ p : X × E, f p = f (p.1, 0) +
        (∫ θ in (0 : ℝ)..1, fderiv ℝ (fun a => f (p.1, a)) (θ • p.2)) p.2 := by
  sorry

end FiniteEnergyPlane
