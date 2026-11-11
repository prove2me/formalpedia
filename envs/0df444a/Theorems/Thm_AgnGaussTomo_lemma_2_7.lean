-- Prove2me | Theorems.Thm_AgnGaussTomo_lemma_2_7
-- name    : AgnGaussTomo.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:04.286934+00:00
-- url     : https://prove2.me/theorems/a4bdd010-9ee0-46f3-9a1a-99b98ddda13a
-- title:
--   Lemma 2.7 — near-vacuum parameter bound $\|(b,A)\|_{\mathcal P}\lesssim d_{\mathrm{tr}}(\psi,0)$
-- statement:
--   There are universal constants $\xi_0>0$ and $C>0$ such that for every $n$ and every $\theta=(b,A)\in\mathcal P_n$ with $\|A\|_{\mathrm{op}}<1$: if the pure Gaussian state $|\psi(b,A)\rangle$ satisfies $d_{\mathrm{tr}}(|\psi\rangle\langle\psi|,|0\rangle\langle0|)\le\xi_0$, then
--
--   $$
--   \|(b,A)\|_{\mathcal P}\le C\,d_{\mathrm{tr}}\big(|\psi(b,A)\rangle\langle\psi(b,A)|,|0\rangle\langle0|\big).
--   $$
--
--   Parameter distance and trace distance are not comparable in general, but near the vacuum they are; this lets the refinement stage work in Bargmann coordinates.
--
--   Differences from the source:
--   - reading: ξ₀ and ≲ → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - encoding: a pure Gaussian state |ψ(b, A)⟩ → psi θ for θ ∈ P_n with ‖A‖_op < 1 (the domain of Fact 2.4); reason: every pure Gaussian state has this form (Fact 2.4) and these are exactly the parameters for which ψ(b, A) is defined
--   - encoding: trace distances → the published BosonicLearn.traceDist (½‖·‖₁) in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: same values on density operators
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 2.7, printed p. 12 (PDF p. 15); proof on p. 13 (PDF p. 16)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_AgnGaussTomo_vacuum
import Definitions.Def_AgnGaussTomo_psi
import Definitions.Def_AgnGaussTomo_opNorm

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Lemma 2.7: near the vacuum, Bargmann parameters are controlled by the trace distance.** Arulandu,
Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov
2026), Lemma 2.7, printed p. 12 (PDF p. 15): "Let |ψ(b, A)⟩ denote a pure Gaussian state which is
near-vacuum, in the sense that d_tr(|ψ⟩⟨ψ|, |0⟩⟨0|) ≤ ξ₀ for some universal constant ξ₀. Then,
‖(b, A)‖_P ≲ d_tr(|ψ⟩⟨ψ|, |0⟩⟨0|)."

**Formalization Note.** `|ψ(b, A)⟩` is `psi θ` for `θ ∈ Pspace n` with `‖A‖_op < 1` (Fact 2.4's
domain, so that `ψ(b, A)` is a pure Gaussian state). `ξ₀` and the constant of `≲` are universal
(before `n`). `‖θ‖` is the paper's `‖(b, A)‖_P` (Eq. (12)). The trace distance is the published
`BosonicLearn.traceDist` in `ℝ≥0∞`. -/
theorem lemma_2_7 : ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (θ : Pspace n), opNorm (Pspace.A θ) < 1 →
      BosonicLearn.traceDist (rankOne (psi θ)) (vacuum n) ≤ ENNReal.ofReal ξ₀ →
      ENNReal.ofReal ‖θ‖ ≤
        ENNReal.ofReal C * BosonicLearn.traceDist (rankOne (psi θ)) (vacuum n) := by sorry

end AgnGaussTomo
