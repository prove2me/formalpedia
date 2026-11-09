-- Prove2me | Theorems.Thm_ElimAgree_lemma_3_3
-- name    : ElimAgree.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:20:09.223998+00:00
-- url     : https://prove2.me/theorems/f2619761-f448-4d3f-9942-93cad71fd3e0
-- title:
--   Lemma 3.3 — tensorization of entropy contraction under arbitrary dependence
-- statement:
--   Let $\kappa_i$ be channels from $X_i$ to $Y_i$ and $\pi_i$ laws on $X_i$ ($i=1,\dots,r$) such that, for a constant $\zeta\ge0$,
--   $$D(P_i\kappa_i\,\|\,\pi_i\kappa_i)\le\zeta\,D(P_i\,\|\,\pi_i)\quad\text{for every law }P_i\text{ on }X_i .$$
--   Then for every joint law $P$ of $(X_1,\dots,X_r)$, with arbitrary dependence between coordinates,
--   $$D\Big(P\bigotimes_i\kappa_i\,\Big\|\,\bigotimes_i\pi_i\kappa_i\Big)\le\zeta\,D\Big(P\,\Big\|\,\bigotimes_i\pi_i\Big).$$
--
--   The input law in §3.3 is far from a product, which is why the joint law is arbitrary.
--
--   **Formalization Note** Relative entropy takes the value $+\infty$ off absolute continuity, and $0\cdot\infty=0$.
--
--   Differences from the source:
--   - reading: ζ with no stated sign → ζ : ℝ≥0; reason: ζ multiplies relative entropies in [0, ∞]; for ζ < 0 the hypothesis forces every X_i to carry a single law and the claim is 0 ≤ 0
--   - encoding: relative entropy in nats with values in [0, ∞] → klDivDiscrete, valued in ℝ≥0∞ (⊤ off absolute continuity); laws as nonnegative real vectors summing to 1; reason: Lean convention; same instances
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Lemma 3.3, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_ElimAgree_IsLaw

open FoundationsRL.GeneralDM

namespace ElimAgree

/-- Lemma 3.3 (Tensorization), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.8: let `κ_i` be channels and `π_i` laws with
`D(P_iκ_i‖π_iκ_i) ≤ ζ D(P_i‖π_i)` for every law `P_i`. Then for every joint law `P` of
`(X_1, …, X_r)`, with arbitrary dependence between coordinates,
`D(P ⊗_i κ_i ‖ ⊗_i π_iκ_i) ≤ ζ D(P ‖ ⊗_i π_i)`.

**Formalization Note.** Relative entropy is `klDivDiscrete` (nats, `⊤` off absolute continuity),
so the hypothesis covers every law `P_i`, including those not absolutely continuous with respect
to `π_i`. The constant `ζ` is a nonnegative real; products in `ℝ≥0∞` use `0 · ⊤ = 0`. -/
theorem lemma_3_3 {r : ℕ} {X Y : Fin r → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]
    (κ : ∀ i, X i → Y i → ℝ) (hκ : ∀ i, IsChannel (κ i))
    (π : ∀ i, X i → ℝ) (hπ : ∀ i, IsLaw (π i)) (ζ : NNReal)
    (hζ : ∀ i (Pi : X i → ℝ), IsLaw Pi →
      klDivDiscrete (pushLaw Pi (κ i)) (pushLaw (π i) (κ i)) ≤ (ζ : ENNReal) * klDivDiscrete Pi (π i))
    (P : (∀ i, X i) → ℝ) (hP : IsLaw P) :
    klDivDiscrete (pushLaw P (tensorChannel κ)) (prodLaw (fun i => pushLaw (π i) (κ i))) ≤
      (ζ : ENNReal) * klDivDiscrete P (prodLaw π) := by sorry

end ElimAgree
