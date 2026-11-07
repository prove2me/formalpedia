-- Prove2me | Theorems.Thm_EffRobustLearn_lemma_3_10
-- name    : EffRobustLearn.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:11.161495+00:00
-- url     : https://prove2.me/theorems/653618da-5aef-4e40-adb9-824c0e0a3114
-- title:
--   Lemma 3.10 — $L(\bar h_T)\le\varepsilon/4$
-- statement:
--   Let $\varepsilon>0$, let the samples be nonempty, and let $(c_t)$ be a trajectory of Algorithm 1 from $c_0\in C$, so that every Frank–Wolfe step satisfies its accuracy guarantee. Then
--   $$L(\bar h_T)=\sup_{c\in C}\Big(\widehat{\mathrm{err}}_{S_{\mathrm{ref}}}(\bar h_T,c)-\sup_{\bar\mu\in\mathrm{conv}(C)}\eta(c,\bar\mu;\bar S_{\mathrm{inp}},S_{\mathrm{ref}})\Big)\le\frac\varepsilon4.$$
--
--   This is the deterministic half of the main theorem.
--
--   Differences from the source:
--   - reading: every Frank–Wolfe step satisfies Eq. (3.3) → line 7's inequality with accuracy $\gamma_t/25$ in the original coordinates; reason: Eq. (3.3) belongs to Theorem 3.4; p.33 applies it after normalizing, with $D_2=2$ and $D_2^2\gamma_t/100=\gamma_t/25$
--   - generalization: $\bar h_T$ produced by Algorithm 1 → any $c_t\in C$ with that guarantee, however they were found; reason: the hypothesis is all the proof uses; a run of Algorithm 1 on the good event is an instance
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Lemma 3.10, eq. (3.9), p.17 (PDF p.18)

import Mathlib
import Definitions.Def_EffRobustLearn_IsAlg1Trajectory
import Definitions.Def_EffRobustLearn_lossL

namespace EffRobustLearn

/-- Lemma 3.10 (Error guarantee), p.17 (arXiv:2609.17655, held version, sha256 312a0857…): if every Frank–Wolfe step of Algorithm 1 satisfies its accuracy guarantee, then
`L(h̄_T) ≤ ε/4`. Deterministic: `IsAlg1Trajectory` does not mention how the `c_t` were found. Any `ε > 0`. -/
theorem lemma_3_10 {X : Type*} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (C : Set (X → Bool)) (ε : ℝ)
    (hε : 0 < ε) (c0 : X → Bool) (c : ℕ → X → Bool) (Sinp : Fin n → X × Bool) (Sref : Fin m → X)
    (htraj : IsAlg1Trajectory C ε c0 c Sinp Sref) :
    lossL C Sinp Sref (hbarSeq ε c0 c) ≤ ε / 4 := by sorry

end EffRobustLearn
