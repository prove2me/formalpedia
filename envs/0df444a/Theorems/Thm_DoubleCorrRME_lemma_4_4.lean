-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_4_4
-- name    : DoubleCorrRME.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:11.131957+00:00
-- url     : https://prove2.me/theorems/72adbb82-ad86-460d-9c28-519b7779149b
-- title:
--   Lemma 4.4 ([APS22, Prop. 4.9]), p.21 — permutation concentration: $\|(Z-\mathbb E Z)_+\|_{L_p}\le O(\sqrt pV+pB_p)$
-- statement:
--   Let $\mathcal A$ be a collection of $m\times m$ real matrices and $\pi$ a uniformly random permutation of $[m]$. Define
--
--   $$Z=\sup_{A\in\mathcal A}\sum_{r=1}^mA_{r,\pi(r)},\quad V=\mathbb E\Big[\sup_{A\in\mathcal A}\Big(\sum_{r=1}^mA_{r,\pi(r)}^2\Big)^{1/2}\Big],\quad B_p=\Big\|\max_{r\in[m]}\sup_{A\in\mathcal A}|A_{r,\pi(r)}|\Big\|_{L_p}.$$
--
--   There is an absolute constant $C$ such that for every $p\ge2$,
--
--   $$\big\|(Z-\mathbb EZ)_+\big\|_{L_p}\le C\big(\sqrt p\,V+p\,B_p\big).$$
--
--   This concentration inequality for suprema of permutation sums drives the bound on the randomly formed batch means.
--
--   **Formalization Note** $\mathcal A$ is nonempty with uniformly bounded entries, so all suprema are finite.
--
--   Differences from the source:
--   - encoding: "a collection of m × m matrices" → a nonempty set 𝒜 with entries bounded by a common M; reason: excludes only collections for which Z, V or B_p is +∞ or an empty supremum, where the inequality is undefined
--   - encoding: O(·) → ∃ C > 0 before m, 𝒜 and p; reason: meaning of an absolute constant
--   - encoding: E and ∥·∥_{L_p} under a uniformly random permutation → finite averages permAvg, permLp over Equiv.Perm (Fin m); reason: the uniform law on a finite group; same values
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 4.4, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_DoubleCorrRME_Perm

namespace DoubleCorrRME

/-- **Lemma 4.4** ([APS22, Proposition 4.9]), p.21 (PDF p.22).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Let 𝒜 be a collection of m × m matrices, and let π be a uniformly random permutation of [m].
Define Z := sup_{A^s∈𝒜} ∑_{r=1}^m A^s_{r,π(r)}. Then, for every p ≥ 2,
∥(Z − E[Z])_+∥_{L_p} ≤ O(√p V + pB_p), where V := E[sup_{A^s∈𝒜} √(∑_{r=1}^m (A^s_{r,π(r)})²)] and
B_p := ∥max_{r∈[m]} sup_{A^s∈𝒜} |A^s_{r,π(r)}|∥_{L_p}."

**Formalization Note.**
* The constant `C` of the `O(·)` is chosen before `m`, `𝒜` and `p`.
* `𝒜` is any nonempty set of real `m × m` matrices whose entries are bounded by one common `M`;
  this only excludes collections for which `Z`, `V` or `B_p` is `+∞` or undefined (an empty
  supremum). Under it every supremum is a real `⨆` of a bounded family. `𝒜` need not be finite.
* `π` is uniform on `Equiv.Perm (Fin m)`; `E` and `∥·∥_{L_p}` are `permAvg` and `permLp`.
  `max_{r∈[m]}` is `⨆ r : Fin m` (equal to `0` when `m = 0`, where every quantity is `0`). -/
theorem lemma_4_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (𝒜 : Set (Matrix (Fin m) (Fin m) ℝ)), 𝒜.Nonempty →
        (∃ M : ℝ, ∀ A ∈ 𝒜, ∀ r s, |A r s| ≤ M) →
        ∀ p : ℝ, 2 ≤ p →
          let Z : Equiv.Perm (Fin m) → ℝ := fun π => ⨆ A : 𝒜, ∑ r, (A : Matrix _ _ ℝ) r (π r)
          let V : ℝ := permAvg m fun π =>
            ⨆ A : 𝒜, Real.sqrt (∑ r, ((A : Matrix _ _ ℝ) r (π r)) ^ 2)
          let Bp : ℝ := permLp m p fun π => ⨆ r : Fin m, ⨆ A : 𝒜, |(A : Matrix _ _ ℝ) r (π r)|
          permLp m p (fun π => max (Z π - permAvg m Z) 0) ≤
            C * (Real.sqrt p * V + p * Bp) := by sorry

end DoubleCorrRME
