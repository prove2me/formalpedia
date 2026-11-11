-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim9_exit_condition
-- name    : ExpanderWalkDecode.Main.claim9_exit_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:23:58.326813+00:00
-- url     : https://prove2.me/theorems/e8ce6ca3-6273-483a-a9d8-54f541683198
-- title:
--   Claim 9 (Exit Condition) — list covering $\ge\rho^2/2$ and near consistency $G(P)\le10/\alpha$
-- statement:
--   Let $Y\in\{\pm1\}$ on the code coordinates, $0<\rho\le1$, $\alpha>0$, $C_{\mathrm{base}}$ a binary linear code with embedding $\iota$, and $P\in\mathcal E$. If $\min_{V\in\mathcal E}\Gamma(P,V)>-\rho^2$, then
--
--   1. (list covering) for every $Z\in\mathrm{LIST}(Y,\rho)$, $\displaystyle\mathbb E_{\vec a\sim\mathrm{WRW}^t_s}\big[Z_{\vec a}\,P_{\vec a,\emptyset}\big]\ge\frac{\rho^2}2$, where $P_{\vec a,\emptyset}=\langle x_{\vec a},x_\emptyset\rangle$;
--   2. (near consistency) $G(P)\le\dfrac{10}{\alpha}$.
--
--   So when the vector-recovery loop exits, its vectors are good.
--
--   Differences from the source:
--   - generalization: the paper's walk structure (graphs of Proposition 3, base code of Proposition 1) → any outer graph with ports F_2^m, any inner Cayley graph on (F_2^m)^s, any t, any base code and embedding; reason: the statement uses no expansion property; specializes to the paper's structure
--   - generalization: α = 10240R²(t+1)³/ρ⁸ → any α > 0; reason: the argument uses only α > 0; specializes
--   - reading: E_{a∼A} E_{⃗a,⃗a′∼WRW^{≤t}_s(a)} in G(P) → ⃗a, ⃗a′ drawn uniformly from the set WRW^{≤t}_s(a); reason: the source gives no other law on walks of mixed lengths; Claim 11's proof bounds sums over WRW^{≤t}_s(a) by R times this average
--   - encoding: min_{V∈E} Γ(P,V) > −ρ² → Γ(P,V) > −ρ² for every V ∈ E; reason: E is compact and Γ(P,·) continuous, so the minimum is attained; equivalent
--   - encoding: Z ∈ LIST(Y, ρ) as an amplified codeword → a base codeword whose padded amplified word has correlation ≥ ρ; reason: same set
--   - generalization: a received word on the support set of wide replacement walks → an arbitrary received sign word on the full latent-coordinate space; reason: a source word pulls back along the walk map; all copies of a support coordinate then have the same received sign. The extension keeps the latent sampling law and charges every coordinate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 14 (PDF p. 17), §4.1, Claim 9

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Decoder

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 9 (Exit Condition) (§4.1, p. 14): if `min_{V ∈ E} Γ(P, V) > -ρ²`, then
`E_{⃗a ∼ WRW^t_s}[Z_⃗a ⟨x_⃗a, x_∅⟩] ≥ ρ²/2` for every `Z ∈ LIST(Y, ρ)` (list covering) and
`G(P) ≤ 10/α` (near consistency). -/
theorem claim9_exit_condition {A : Type} [Fintype A] {m s q : ℕ} (G : RotGraph A (Fin m → ZMod 2))
    (u : Fin q → Inner m s) (t : ℕ) (Y : Latent A m s q t → ℝ) (ρ α : ℝ)
    (hY : ∀ l, Y l = 1 ∨ Y l = -1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hα : 0 < α)
    {n : ℕ} (ι : Fin n ↪ A) (Cb : BinaryLinearCode n)
    (P : Matrix (WIdx G u t) (WIdx G u t) ℝ) (hP : P ∈ Ell G u t)
    (hexit : ∀ V ∈ Ell G u t, -ρ ^ 2 < Gamma G u t α Y ρ P V) :
    (∀ z ∈ listSet G u t ι Cb Y ρ,
      ρ ^ 2 / 2 ≤ avg fun l : Latent A m s q t =>
        ampProd (pad ι z) (walk G u l) * P (walkW G u t l) (emptyW G u t)) ∧
    Gpot G u t P ≤ 10 / α := by sorry

end ExpanderWalkDecode.Main
