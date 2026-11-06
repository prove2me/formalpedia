-- Prove2me | Theorems.Thm_DecodablePOMDP_lemma_7
-- name    : DecodablePOMDP.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:08.229821+00:00
-- url     : https://prove2.me/theorems/6934dd82-96d7-44fc-9d62-f6faf0aff4c6
-- title:
--   Lemma 7 — $w\mapsto\Phi_h(u,w)$ is an $\ell_1$ isometry
-- statement:
--   Let $\mathcal P$ be a valid POMDP, $\rho\in(0,1]$, $D_h$ decoders with $d_{h,s}\ge\rho$, $L\ge1$, $h\in[1:H]$ and $u\in\mathcal U_h$. For all $w,w'\in\Delta(\mathcal Q)$,
--
--   $$\|\Phi_h(u,w)-\Phi_h(u,w')\|_1=\|w-w'\|_1.\tag{14}$$
--
--   Rounding errors in the weights are therefore exactly rounding errors in the represented beliefs.
--
--   Differences from the source:
--   - encoding: "a fixed stage-suffix pair (h, u)" → h ∈ [1 : H], u ∈ U_h; the left norm over (S × Q) ∪ {∂}; reason: stages and suffixes of the planner; Φ_h(u, ·) vanishes at ∂
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Lemma 7, p.17

import Mathlib
import Definitions.Def_DecodablePOMDP_Admissible

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Lemma 7 — `w ↦ Φ_h(u, w)` is an ℓ₁ isometry.** Let `P` be a valid POMDP, `ρ ∈ (0, 1]`, `D_h`
decoders with `d_{h,s} ≥ ρ`, `L ≥ 1`, `h ∈ [1 : H]` and `u` a suffix of stage `h`. For all
`w, w′ ∈ Δ(Q)`, `‖Φ_h(u, w) − Φ_h(u, w′)‖₁ = ‖w − w′‖₁`, the left norm over the killed states
`(S × Q) ∪ {∂}`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 7, p.17: "For a fixed stage-suffix pair
(h, u), for any w, w′ ∈ ∆(Q), the belief Φh(u, ·) is an isometry in the 1-norm, i.e.,
∥Φh(u, w) − Φh(u, w′)∥1 = ∥w − w′∥1. (14)" -/
theorem lemma_7 {S A O : Type} [Fintype S] [Fintype O] [DecidableEq S]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (hP : P.IsValid)
    (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L)
    (h : ℕ) (hh1 : 1 ≤ h) (hhH : h ≤ P.H) (u : Suffix A O S) (hu : IsSuffixAt L h u)
    (w w' : Option (Fin L) → ℝ) (hw : IsDist w) (hw' : IsDist w') :
    ∑ ξ, |Phi P D ρ L h u w ξ - Phi P D ρ L h u w' ξ| = ∑ q, |w q - w' q| := by sorry

end DecodablePOMDP
