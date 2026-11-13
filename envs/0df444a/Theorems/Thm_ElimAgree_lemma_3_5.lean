-- Prove2me | Theorems.Thm_ElimAgree_lemma_3_5
-- name    : ElimAgree.lemma_3_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:15:48.288265+00:00
-- url     : https://prove2.me/theorems/40bc85d4-0f3b-41bb-9fd7-72cc554f367c
-- title:
--   Lemma 3.5 — $-(r_1-r_0)(c_1-c_0)\le2c_0(\sqrt{r_1}-\sqrt{r_0})^2+2r_0(\sqrt{c_1}-\sqrt{c_0})^2$
-- statement:
--   For nonnegative reals $r_0,r_1,c_0,c_1$,
--   $$-(r_1-r_0)(c_1-c_0)\le2c_0\big(\sqrt{r_1}-\sqrt{r_0}\big)^2+2r_0\big(\sqrt{c_1}-\sqrt{c_0}\big)^2 .$$
--
--   Applied pointwise to the identity (3.3), it turns the product of two deviations into Hellinger terms.
--
--   Differences from the source: none.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Lemma 3.5, p.9 (PDF p.11)

import Mathlib

namespace ElimAgree

/-- Lemma 3.5, Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.9: for nonnegative `r_0, r_1, c_0, c_1`,
`−(r_1 − r_0)(c_1 − c_0) ≤ 2c_0(√r_1 − √r_0)² + 2r_0(√c_1 − √c_0)²`. -/
theorem lemma_3_5 (r₀ r₁ c₀ c₁ : ℝ) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) :
    -((r₁ - r₀) * (c₁ - c₀)) ≤
      2 * c₀ * (Real.sqrt r₁ - Real.sqrt r₀) ^ 2 + 2 * r₀ * (Real.sqrt c₁ - Real.sqrt c₀) ^ 2 := by sorry

end ElimAgree
