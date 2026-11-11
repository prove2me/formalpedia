-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim10_approximate_action
-- name    : ExpanderWalkDecode.Main.claim10_approximate_action
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:23:42.752194+00:00
-- url     : https://prove2.me/theorems/68ea8ee8-1d6d-4cac-9ad7-cba91bd51c8b
-- title:
--   Claim 10 — approximate action $\|T_ax_{\vec a_{\mathrm{tail}}}-x_{\vec a}\|^2\le\theta+\theta^{-1}\sum\langle\cdot,\cdot\rangle^2$
-- statement:
--   Let $\{x_{\vec a}\}$ be any vectors in $\mathbb R^d$ indexed by $\mathrm{WRW}^{\le t}_s$, $\rho>0$, $\theta=\rho^4/(32(t+1)^2)$, and $T_a=2\Pi_a-I$ the operators of Figure 3. For every $a\in A$ and $\vec a\in\mathrm{WRW}^{\le t}_s(a)$,
--   $$\big\|T_ax_{\vec a_{\mathrm{tail}}}-x_{\vec a}\big\|^2\le\theta+\theta^{-1}\sum_{\vec a'\in\mathrm{WRW}^{\le t}_s(a)}\big\langle x_{\vec a}-x_{\vec a_{\mathrm{tail}}},\,x_{\vec a'}+x_{\vec a'_{\mathrm{tail}}}\big\rangle^2 .$$
--
--   The reflection $T_a$ approximately multiplies by the parity of the first vertex, with an error controlled by the local inconsistency.
--
--   Differences from the source:
--   - generalization: the paper's walk structure (graphs of Proposition 3, base code of Proposition 1) → any outer graph with ports F_2^m, any inner Cayley graph on (F_2^m)^s, any t, any base code and embedding; reason: the statement uses no expansion property; specializes to the paper's structure
--   - encoding: ‖v‖² → v ⬝ᵥ v; reason: same number
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 15 (PDF p. 18), §4.2, Claim 10

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Decoder

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 10 (Approximate Action of `T_a`) (§4.2, p. 15): for the operators `T_a` of Figure 3,
every `a ∈ A` and every `⃗a ∈ WRW^{≤t}_s(a)`,
`‖T_a x_{⃗a_tail} - x_⃗a‖² ≤ θ + θ⁻¹ ∑_{⃗a′ ∈ WRW^{≤t}_s(a)} ⟨x_⃗a - x_{⃗a_tail}, x_{⃗a′} + x_{⃗a′_tail}⟩²`,
`θ = ρ⁴/(32(t+1)²)`. -/
theorem claim10_approximate_action {A : Type} [Fintype A] {m s q t d : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (x : WIdx G u t → Fin d → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (a : A) (w : WIdx G u t) (hw : w ∈ fromW G u t a) :
    (figure3T G u x ρ a *ᵥ x (tailW G u t w) - x w) ⬝ᵥ (figure3T G u x ρ a *ᵥ x (tailW G u t w) - x w)
      ≤ thetaOp ρ t + (thetaOp ρ t)⁻¹ * ∑ w' ∈ fromW G u t a,
          ((x w - x (tailW G u t w)) ⬝ᵥ (x w' + x (tailW G u t w'))) ^ 2 := by sorry

end ExpanderWalkDecode.Main
