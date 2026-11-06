-- Prove2me | Theorems.Thm_DecodablePOMDP_lemma_1
-- name    : DecodablePOMDP.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:59.645461+00:00
-- url     : https://prove2.me/theorems/8387eba1-e3d7-4d36-be1b-307f9bb32af2
-- title:
--   Lemma 1 — the augmented POMDP has the same optimal value
-- statement:
--   Let $\mathcal P$ be a valid POMDP with a nonempty action set and let $D_h$, $h\in[2:H]$, be decoders (each $D_h(\cdot\mid y)$ a probability vector). The augmented POMDP $\widehat{\mathcal P}$, which also reveals the decoder's guess $\widehat X_h\sim D_h(\cdot\mid Y_h)$, has the same optimal value:
--
--   $$V^*_{\widehat{\mathcal P}}=V^*_{\mathcal P}.$$
--
--   The extra coordinate carries no information beyond $Y_h$; this lets the analysis work in $\widehat{\mathcal P}$.
--
--   Differences from the source:
--   - generalization: D_h "an optimal decoder" (§3, p.6) → any decoder family (`IsDecoderFamily P D`); reason: the proof in A.1 uses no optimality and no decodability; optimal decoders are a special case
--   - encoding: action space of size A (implicitly A ≥ 1) → `[Nonempty A]`; reason: with no action there is no policy; the paper's A ≥ 1
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Lemma 1, p.7 (proof A.1, p.14)

import Mathlib
import Definitions.Def_DecodablePOMDP_Value
import Definitions.Def_DecodablePOMDP_Augmented

namespace DecodablePOMDP

/-- **Lemma 1 — the augmented POMDP has the same optimal value.** For every valid POMDP `P` with a
nonempty action set and every family of decoders `D_h` (each `D_h(· | y)` a probability vector),
the augmented POMDP `P̂` with observations `(Y_h, X̂_h)` satisfies `V*_{P̂} = V*_P`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 1, p.7: "The augmented POMDP P̂ with
observation Zh = (Yh, X̂h) has the same optimal value as the original POMDP P; i.e., V∗_{P̂} = V∗_P."

**Formalization Note.** Stated for every decoder family, not only the optimal decoders of §3 (the
proof in A.1 uses no optimality). -/
theorem lemma_1 {S A O : Type} [Fintype S] [Fintype A] [Fintype O] [Nonempty A]
    (P : POMDP S A O) (D : ℕ → O → S → ℝ) (hP : P.IsValid) (hD : IsDecoderFamily P D) :
    optValue (augmented P D) = optValue P := by sorry

end DecodablePOMDP
