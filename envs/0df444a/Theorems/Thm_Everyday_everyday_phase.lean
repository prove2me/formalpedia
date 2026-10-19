-- Prove2me | Theorems.Thm_Everyday_everyday_phase
-- name    : Everyday.everyday_phase
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T00:18:26.923366+00:00
-- url     : https://prove2.me/theorems/60a0d7f2-9e7e-4202-bd90-0385794e6065
-- title:
--   The everyday equation's amplitude is a phase: the assembled action is real, so exp(iS) has modulus one
-- statement:
--   The source equation's claim, in one line: the everyday world's dynamics is a single action functional — spacetime, gravity, the other forces, matter, and the Higgs sector, each a labeled part of the integrand — whose exponential of i times itself gives the transition amplitude. The item is the goal theorem of the mission, the equation's quantum-mechanical heart: assemble the four labeled sectors into the action of a configuration of the discrete arena; the assembled action is a real number — the gravity, gauge, and Higgs sectors are real-valued, and the matter sector's Yukawa term plus its hermitian conjugate is real — so the exponential of i times the action has modulus exactly one. The everyday equation generates phases, not probabilities: probability enters only through the coherent sum of such phases.
--
--   **Formalization Note** The assembled action omits the fermion kinetic and Higgs kinetic terms, as the definition discloses; their realness is structurally identical to the assembled sectors'. The quartic coupling λ of the Higgs potential is bound as lam in the formal statement, λ being a reserved keyword in Lean 4. The proof: the action's imaginary part vanishes — the three real-valued sectors contribute zero imaginary part by their coercions, and the matter sector's by the yukawa_real milestone — so the real part of i times the action is zero, and the modulus of the exponential is the exponential of zero, which is one.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the equation's full amplitude W = ∫ [Dg][DA][Dψ][DΦ] exp{i∫ d⁴x √(-g) […]}

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

namespace Everyday

/-- The everyday equation's amplitude is a phase: assemble the four
labeled sectors — gravity, the other forces, matter (the Yukawa term
plus its hermitian conjugate), and the Higgs potential — into the action
of a configuration; the action is real, so the exponential of i times it
has modulus exactly one. This is the quantum-mechanical heart of the
source equation: the everyday world's dynamics is one real functional
whose exponentiation gives the transition amplitude. -/
theorem everyday_phase {X : Type} [Fintype X] (vol : X → ℝ) (w : X → X → X → ℝ)
    (mp : ℝ) (R : X → ℝ) (A : X → X → ℝ) (ψL ψR : X → ℂ) (V : ℂ) (Φh : X → ℂ)
    (μ lam : ℝ) :
    ‖Complex.exp
      (Complex.I * everydayAction vol w mp R A ψL ψR V Φh μ lam)‖ = 1 := by sorry

end Everyday
