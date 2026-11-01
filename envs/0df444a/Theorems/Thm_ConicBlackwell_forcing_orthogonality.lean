-- Prove2me | Theorems.Thm_ConicBlackwell_forcing_orthogonality
-- name    : ConicBlackwell.forcing_orthogonality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:52.235635+00:00
-- url     : https://prove2.me/theorems/98dd7486-b2cf-493d-9c66-4d4f4aee0fe9
-- title:
--   The forcing identity $\langle u_t,v_{t+1}\rangle=0$ of CBA$^+$ (p.9)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a nonempty convex compact set, $\kappa=\max_{x\in\mathcal X}\|x\|_2$, $\mathcal C=\operatorname{cone}(\{\kappa\}\times\mathcal X)$, and $x_0\in\mathcal X$. For every $u\in\mathcal C$ and every loss $f\in\mathbb R^n$, the decision $x=\mathrm{CHOOSEDECISION}_{\mathrm{CBA}^+}(u)$ makes the next payoff $v=(\langle f,x\rangle/\kappa,\,-f)$ orthogonal to $u$:
--
--   $$
--   \big\langle u,\ (\langle f,x\rangle/\kappa,\,-f)\big\rangle=0 .
--   $$
--
--   Applied to $u=u_t\in\mathcal C$ and $f=f_{t+1}$ this is the paper's $\langle u_t,v_{t+1}\rangle=0$: the decision forces the new payoff into the hyperplane orthogonal to the aggregate payoff, as in Blackwell's approachability.
--
--   Differences from the source:
--   - generalization: u = u_t, the aggregate payoff of the CBA+ run → any u ∈ C = cone({κ} × X); reason: the run's u_t lies in C because of the projection step (p.5), so the run's identity is the case u = u_t
--   - encoding: ℝⁿ and ℝ × ℝⁿ = ℝⁿ⁺¹ → E n = EuclideanSpace ℝ (Fin n), and lift a x : E (n+1) with the scalar a in coordinate 0; reason: Lean convention of the reused ApproachRegret.ToOLO definitions; same instances (the dimension n = 0 is not excluded; there X ⊆ {0} and the statements stay true)
--   - encoding: κ = max_{x∈X} ‖x‖₂ and v_t = (⟨f_t, x_t⟩/κ, −f_t) → kappa X = sSup of ‖x‖ over X, and payoff X x f = lift (⟪f, x⟫ / kappa X) (−f) with Lean's x/0 = 0; reason: sSup is the max on a nonempty compact X; κ = 0 only when X = {0}, where the page's ⟨f,x⟩/κ is undefined and both coordinates conventions give the same statement
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), proof of Theorem 3.3, p.9 (⟨u_t, v_{t+1}⟩ = 0); cf. (10) and the computation below it, p.8

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Definitions.Def_ConicBlackwell_chooseDecision
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The forcing identity `⟨u_t, v_{t+1}⟩ = 0`**, Grand-Clément & Kroer, arXiv:2202.12277v1, p.9 ("By construction and for the
same reason as for (10), ⟨u_t, v_{t+1}⟩ = 0"); cf. (10) and the computation below it, p.8.
For every `u ∈ C = cone({κ} × X)` and every loss `f`, the payoff of the decision
`CHOOSEDECISION_{CBA+}(u)` is orthogonal to `u`.

Formalization Note: stated for an arbitrary `u ∈ C` (the run's `u_t` lies in `C`); `x₀ ∈ X` is
the arbitrary point used when `ũ = 0`. -/
theorem forcing_orthogonality {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x₀ : E n) (hx₀ : x₀ ∈ X) (u : E (n + 1)) (hu : u ∈ cone (lift (kappa X) '' X))
    (f : E n) :
    ⟪u, payoff X (chooseDecision X x₀ u) f⟫ = 0 := by sorry

end ConicBlackwell
