-- Prove2me | Theorems.Thm_FamousTheorems_mcshane_lipschitz_extension
-- name    : FamousTheorems.mcshane_lipschitz_extension
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:33.054361+00:00
-- url     : https://prove2.me/theorems/74600d5c-2f08-46ad-af1b-e017309e9324
-- title:
--   The McShane extension theorem (Lipschitz functions)
-- statement:
--   **The McShane extension theorem.** Let $s$ be a subset of a (pseudo)metric space $\alpha$ and $f:s\to\mathbb R$ a $K$-Lipschitz function. Then $f$ extends to a $K$-Lipschitz function $g:\alpha\to\mathbb R$ on the whole space.
--
--   An explicit extension is $g(x)=\inf_{y\in s}\big(f(y)+K\,d(x,y)\big)$ (McShane, 1934, and independently Whitney). The extension preserves the Lipschitz constant exactly, which fails in general for vector-valued maps (where Kirszbraun's theorem is the Hilbert space substitute).
--
--   **Formalization note.** Mathlib's `LipschitzOnWith.extend_real`. The function is given as `f : α → ℝ` that is `K`-Lipschitz on `s`, with `K : NNReal`, and the conclusion asks for a globally `K`-Lipschitz `g` agreeing with `f` on `s` (`Set.EqOn f g s`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LipschitzOnWith.extend_real`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mcshane_lipschitz_extension {α : Type*} [PseudoMetricSpace α] {f : α → ℝ} {s : Set α} {K : NNReal} (hf : LipschitzOnWith K f s) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ Set.EqOn f g s := by sorry

end FamousTheorems
