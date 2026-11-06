-- Prove2me | Theorems.Thm_DecodablePOMDP_lemma_3
-- name    : DecodablePOMDP.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:02.954246+00:00
-- url     : https://prove2.me/theorems/e208ac72-fef0-4fc9-b91a-2bfdbfe8ce49
-- title:
--   Lemma 3 — killing costs at most $H^2(1-c)^L$, and killed policies extend
-- statement:
--   Let $\mathcal P$ be a valid POMDP with a nonempty action set, $\rho\in(0,1]$, $c=\rho/2$, $D_h$ decoders with $d_{h,s}\ge\rho$ and $L\ge1$ an integer. Let $V^*=V^*_{\mathcal P}$ and $V^*_L$ the optimal value of $\widetilde{\mathcal P}(L)$. Then
--
--   $$V^*\le V^*_L+H^2(1-c)^L.\tag{4}$$
--
--   Moreover, every randomised policy $\pi_L$ of $\widetilde{\mathcal P}(L)$ extends (App. A.3) to a policy $\pi$ of $\widehat{\mathcal P}$ with $V^\pi_{\widehat{\mathcal P}}\ge V^{\pi_L}_L$; consequently, if $V^{\pi_L}_L\ge V^*_L-\eta_0$ for some $\eta_0\ge0$, then
--
--   $$V^\pi_{\widehat{\mathcal P}}\ \ge\ V^*-H^2(1-c)^L-\eta_0.$$
--
--   This reduces approximate planning for $\mathcal P$ to approximate planning for the killed POMDP.
--
--   Differences from the source:
--   - generalization: π_L "can be extended to a policy π" → the explicit extension of A.3 (`extendPolicy`); reason: an explicit extension implies the existential statement
--   - encoding: V* = optimal value of P, "and equivalently" of P̂ → V* is `optValue P`; reason: the two are equal by Lemma 1; the paper's V* is that of P
--   - generalization: standing assumptions of §3 (ρ ∈ (0, 1], an optimal decoder D_h with (D_h K_h)_{s,s} ≥ ρ, integer L ≥ 1) → any decoder family with d_{h,s} ≥ ρ (`IsRhoDecoderFamily P D ρ`), `0 < ρ ≤ 1`, `1 ≤ L` and `P.IsValid`; reason: the section's standing assumptions (pp.6–8) written as binders; the proofs never use optimality of D_h, so the paper's optimal decoders are a special case
--   - encoding: action space of size A (implicitly A ≥ 1) → `[Nonempty A]`; reason: with no action there is no policy; the paper's A ≥ 1
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Lemma 3, pp.8–9 (proof A.3, p.15)

import Mathlib
import Definitions.Def_DecodablePOMDP_Killed

namespace DecodablePOMDP

/-- **Lemma 3 — killing costs at most `H²(1 − c)^L`, and killed policies extend.** Let `P` be a
valid POMDP with a nonempty action set, `ρ ∈ (0, 1]`, `D_h` decoders with `d_{h,s} ≥ ρ`,
`c = ρ/2`, and `L ≥ 1` an integer. Then
1. `V* ≤ V*_L + H²(1 − c)^L`, where `V* = V*_P` and `V*_L` is the optimal value of `P̃(L)`;
2. every randomised policy `π_L` of `P̃(L)` extends (A.3) to a policy `π` of `P̂` with
   `V^π_{P̂} ≥ V^{π_L}_L`;
3. if moreover `V^{π_L}_L ≥ V*_L − η₀` for some `η₀ ≥ 0`, then `V^π_{P̂} ≥ V* − H²(1 − c)^L − η₀`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 3, pp.8–9: "Let V∗ be the optimal value
of the original POMDP P, and equivalently, V∗ is the optimal value of the augmented POMDP P̂. Let
V∗L be the optimal value of the killed POMDP P̃(L). Then V∗ ≤ V∗L + H²(1 − c)^L. (4) Moreover, if πL
is a policy for the killed POMDP, it can be extended to a policy π for the augmented POMDP such that
V^π ≥ V^{πL}_L. Consequently, if V^{πL}_L ≥ V∗L − η0 for some η0 ≥ 0, then
V^π ≥ V∗ − H²(1 − c)^L − η0."

**Formalization Note.** `V*` is `V*_P` (equal to `V*_{P̂}` by Lemma 1); the extension is the map
of A.3, p.15 (`extendPolicy`). -/
theorem lemma_3 {S A O : Type} [Fintype S] [Fintype A] [Fintype O] [DecidableEq S] [Nonempty A]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (ρ : ℝ) (L : ℕ) (hP : P.IsValid)
    (hD : IsRhoDecoderFamily P D ρ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 1 ≤ L) :
    optValue P ≤ optValue (killed P D ρ L) + (P.H : ℝ) ^ 2 * (1 - ρ / 2) ^ L ∧
    (∀ πL : PolicyFn A (Option (O × S)), IsRandPolicy πL →
      value (killed P D ρ L) πL ≤ value (augmented P D) (extendPolicy πL)) ∧
    (∀ πL : PolicyFn A (Option (O × S)), IsRandPolicy πL → ∀ η₀ : ℝ, 0 ≤ η₀ →
      optValue (killed P D ρ L) - η₀ ≤ value (killed P D ρ L) πL →
      optValue P - (P.H : ℝ) ^ 2 * (1 - ρ / 2) ^ L - η₀ ≤
        value (augmented P D) (extendPolicy πL)) := by sorry

end DecodablePOMDP
