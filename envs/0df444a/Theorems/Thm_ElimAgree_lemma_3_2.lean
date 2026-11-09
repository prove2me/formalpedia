-- Prove2me | Theorems.Thm_ElimAgree_lemma_3_2
-- name    : ElimAgree.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:21:25.193194+00:00
-- url     : https://prove2.me/theorems/cbb00ca3-fd86-49b1-9d61-d7f41f377880
-- title:
--   Lemma 3.2 — one half-set: $D(P\kappa_\pm\|u_1)\le\frac1\ell D(P\|u_\ell)$
-- statement:
--   Let $U$ be a finite set with $|U|=2\ell$, $\ell\ge1$, let $u_\ell$ be the uniform law on $\binom U\ell$ and $u_1$ the uniform law on $U$. For every law $P$ on $\binom U\ell$ and either sign,
--   $$D(P\kappa_\pm\,\|\,u_1)\le\frac1\ell\,D(P\,\|\,u_\ell),$$
--   where $D(\cdot\|\cdot)$ is relative entropy in nats and $\kappa_\pm$ are the half-set channels.
--
--   This is the one-coordinate contraction that Lemma 3.3 tensorizes.
--
--   Differences from the source:
--   - encoding: |U| = 2ℓ with 1/ℓ in the bound (ℓ ≥ 1 implicit) → hypothesis 1 ≤ ℓ; reason: for ℓ = 0 the set U is empty and carries no law, and 1/ℓ is undefined
--   - encoding: relative entropy in nats with values in [0, ∞] → klDivDiscrete, valued in ℝ≥0∞ (⊤ off absolute continuity); laws as nonnegative real vectors summing to 1; reason: Lean convention; same instances
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Lemma 3.2, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_ElimAgree_IsLaw
import Definitions.Def_ElimAgree_halfSetChannel

open FoundationsRL.GeneralDM

namespace ElimAgree

/-- Lemma 3.2 (One half-set), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.8: for a set `U` of size `2ℓ`, every law `P` on
`(U choose ℓ)` and either sign, `D(Pκ±‖u_1) ≤ (1/ℓ) D(P‖u_ℓ)`, where `u_ℓ` is uniform on
`(U choose ℓ)`, `u_1` is uniform on `U`, and `D` is relative entropy in nats.

**Formalization Note.** `s = true` is `κ+`, `s = false` is `κ−`. `1 ≤ ℓ` is assumed: for
`ℓ = 0` the set `U` is empty and carries no law on it, and `1/ℓ` is undefined. Relative entropy
is `klDivDiscrete`, valued in `ℝ≥0∞`. -/
theorem lemma_3_2 {U : Type} [Fintype U] [DecidableEq U] (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hU : Fintype.card U = 2 * ℓ) (P : LSet U ℓ → ℝ) (hP : IsLaw P) (s : Bool) :
    klDivDiscrete (pushLaw P (halfSetChannel ℓ s)) (uniformLaw U) ≤
      (ℓ : ENNReal)⁻¹ * klDivDiscrete P (uniformLaw (LSet U ℓ)) := by sorry

end ElimAgree
