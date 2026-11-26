-- Prove2me | Theorems.Thm_EdenVerified_D04_polynomial_field
-- name    : EdenVerified.D04_polynomial_field
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:26:27.78227+00:00
-- url     : https://prove2.me/theorems/c306a259-d097-4242-8137-bb1d10bab86a
-- title:
--   Eden Verified: D04 polynomial field
-- statement:
--   The explicitly displayed field is smooth and has degree exactly five.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L530-L543
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L530-L543

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D04_polynomial_field (c : ℝ) :
    (∀ p : PhaseSpace, vectorField c p =
      !₂[q (radiusSq₁ p) * p 0 - p 1, q (radiusSq₁ p) * p 1 + p 0,
        q (radiusSq₂ p) * p 2 - Real.sqrt 2 * p 3,
        q (radiusSq₂ p) * p 3 + Real.sqrt 2 * p 2, -c * p 4]) ∧
    (∀ (p : PhaseSpace) (i : Fin 5),
      MvPolynomial.eval p (vectorFieldPolynomial c i) = vectorField c p i) ∧
    (∀ i : Fin 5, (vectorFieldPolynomial c i).totalDegree ≤ 5) ∧
    (vectorFieldPolynomial c 0).totalDegree = 5 ∧
    Finset.univ.sup (fun i => (vectorFieldPolynomial c i).totalDegree) = 5 ∧
    (∀ n : WithTop ℕ∞, ContDiff ℝ n (vectorField c)) := by sorry
