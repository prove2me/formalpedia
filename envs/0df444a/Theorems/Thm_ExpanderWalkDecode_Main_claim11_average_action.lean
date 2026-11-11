-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim11_average_action
-- name    : ExpanderWalkDecode.Main.claim11_average_action
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:00.841337+00:00
-- url     : https://prove2.me/theorems/78468605-c388-4315-9dff-c1b72b01aa2b
-- title:
--   Claim 11 — average $t$-length action $(\mathbb E\|T_{a_0}\cdots T_{a_t}x_\emptyset-x_{\vec a}\|)^2\le(t+1)^2\theta+\frac{(t+1)R^2}{\theta}G(P)$
-- statement:
--   Let $A$ be locally invertible, $\{x_{\vec a}\}$ any vectors in $\mathbb R^d$ indexed by $\mathrm{WRW}^{\le t}_s$ with Gram matrix $P$, $\rho>0$, $\theta=\rho^4/(32(t+1)^2)$, $R\ge|\mathrm{WRW}^{\le t}_s(a)|$ for every $a$, and $T_a$ the operators of Figure 3. Then
--   $$\Big(\mathbb E_{\vec a\sim\mathrm{WRW}^t_s}\big\|T_{a_0}T_{a_1}\cdots T_{a_t}x_\emptyset-x_{\vec a}\big\|\Big)^2\le(t+1)^2\theta+\frac{(t+1)R^2}{\theta}\,G(P).$$
--   The square is outside the expectation, as printed.
--
--   With $G(P)\le10/\alpha$ the right side is $\rho^4/16$, which gives the level-$t$ agreement of Lemma 2.
--
--   Differences from the source:
--   - generalization: the paper's walk structure → any walk structure whose outer graph is locally invertible, any vectors; reason: the argument uses local invertibility (the standing property of the outer graph, Appendix B.1) and nothing else of the construction; specializes
--   - reading: E_{a∼A} E_{⃗a,⃗a′∼WRW^{≤t}_s(a)} in G(P) → ⃗a, ⃗a′ drawn uniformly from the set WRW^{≤t}_s(a); reason: the source gives no other law on walks of mixed lengths; Claim 11's proof bounds sums over WRW^{≤t}_s(a) by R times this average
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 16 (PDF p. 19), §4.2, Claim 11

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Decoder

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 11 (Approximate Average `t`-length Action) (§4.2, p. 16): for the operators of Figure 3,
`(E_{⃗a ∼ WRW^t_s} ‖T_{a₀} ⋯ T_{a_t} x_∅ - x_⃗a‖)² ≤ (t+1)² θ + ((t+1) R²/θ) G(P)`, where `P` is the
Gram matrix of the vectors, `θ = ρ⁴/(32(t+1)²)` and `R ≥ |WRW^{≤t}_s(a)|` for every `a`. The
square is outside the expectation, as printed. -/
theorem claim11_average_action {A : Type} [Fintype A] {m s q t d : ℕ}
    (G : RotGraph A (Fin m → ZMod 2)) (u : Fin q → Inner m s) (x : WIdx G u t → Fin d → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (R : ℕ) (hR : ∀ a, (fromW G u t a).card ≤ R)
    (hinv : G.LocallyInvertible) :
    (avg fun l : Latent A m s q t =>
        Real.sqrt ((prodU (figure3T G u x ρ) (walk G u l) *ᵥ x (emptyW G u t) - x (walkW G u t l)) ⬝ᵥ
          (prodU (figure3T G u x ρ) (walk G u l) *ᵥ x (emptyW G u t) - x (walkW G u t l)))) ^ 2
      ≤ ((t : ℝ) + 1) ^ 2 * thetaOp ρ t
        + ((t : ℝ) + 1) * (R : ℝ) ^ 2 / thetaOp ρ t * Gpot G u t (gram G u t x) := by sorry

end ExpanderWalkDecode.Main
