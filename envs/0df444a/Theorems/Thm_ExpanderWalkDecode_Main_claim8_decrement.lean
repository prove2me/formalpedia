-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim8_decrement
-- name    : ExpanderWalkDecode.Main.claim8_decrement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:23:48.946379+00:00
-- url     : https://prove2.me/theorems/af7c4162-73c1-439a-ae65-c0e11784be83
-- title:
--   Claim 8 (Decrement) — a good gradient step lowers $J$ by $\rho^4/(16(4+64\alpha))$
-- statement:
--   Let $Y\in\{\pm1\}$ on the code coordinates, $0<\rho\le1$, $\alpha>0$, and let $J=F+\alpha G$ and $\Gamma$ be as in Definition 3. If $P,Q\in\mathcal E$ satisfy $\Gamma(P,Q)\le-\rho^2/2$, then for $\gamma=\frac{\rho^2}{4(4+64\alpha)}$ and $P'=(1-\gamma)P+\gamma Q$,
--   $$J(P')\le J(P)-\frac{\rho^4}{16(4+64\alpha)} .$$
--
--   Since $0\le J\le9$ at the start of Figure 2, this bounds the number of updates of the vector-recovery loop.
--
--   Differences from the source:
--   - generalization: the paper's walk structure (graphs of Proposition 3, base code of Proposition 1) → any outer graph with ports F_2^m, any inner Cayley graph on (F_2^m)^s, any t, any base code and embedding; reason: the statement uses no expansion property; specializes to the paper's structure
--   - generalization: α = 10240R²(t+1)³/ρ⁸ → any α > 0; reason: the argument uses only α ≥ 0; specializes
--   - reading: E_{a∼A} E_{⃗a,⃗a′∼WRW^{≤t}_s(a)} in G(P) → ⃗a, ⃗a′ drawn uniformly from the set WRW^{≤t}_s(a); reason: the source gives no other law on walks of mixed lengths; Claim 11's proof bounds sums over WRW^{≤t}_s(a) by R times this average
--   - encoding: Γ(P,Q) = ∇J(P)•(Q−P) → the derivative of γ ↦ J(P + γ(Q−P)) at 0; reason: J is a polynomial in the entries; same number
--   - generalization: a received word on the support set of wide replacement walks → an arbitrary received sign word on the full latent-coordinate space; reason: a source word pulls back along the walk map; all copies of a support coordinate then have the same received sign. The extension keeps the latent sampling law and charges every coordinate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 13 (PDF p. 16), §4.1, Claim 8

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Decoder

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 8 (Decrement) (§4.1, p. 13): if `P, Q ∈ E` and `Γ(P, Q) ≤ -ρ²/2`, then for
`γ = ρ²/(4(4+64α))` and `P′ = (1-γ)P + γQ`, `J(P′) ≤ J(P) - ρ⁴/(16(4+64α))`. -/
theorem claim8_decrement {A : Type} [Fintype A] {m s q : ℕ} (G : RotGraph A (Fin m → ZMod 2))
    (u : Fin q → Inner m s) (t : ℕ) (Y : Latent A m s q t → ℝ) (ρ α : ℝ)
    (hY : ∀ l, Y l = 1 ∨ Y l = -1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hα : 0 < α)
    (P Q : Matrix (WIdx G u t) (WIdx G u t) ℝ) (hP : P ∈ Ell G u t) (hQ : Q ∈ Ell G u t)
    (hΓ : Gamma G u t α Y ρ P Q ≤ -ρ ^ 2 / 2) :
    Jpot G u t α Y ρ ((1 - gammaStep α ρ) • P + gammaStep α ρ • Q) ≤
      Jpot G u t α Y ρ P - ρ ^ 4 / (16 * (4 + 64 * α)) := by sorry

end ExpanderWalkDecode.Main
