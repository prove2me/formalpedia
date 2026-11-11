-- Prove2me | Theorems.Thm_ContinualHardness_Linear_lemma_A_7
-- name    : ContinualHardness.Linear.lemma_A_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:12:53.618204+00:00
-- url     : https://prove2.me/theorems/1c1634cd-2111-444c-95a8-778f37af08f6
-- title:
--   Lemma A.7 — decodability: accuracy above 1/2 + δ/2 on task s forces a heavy coordinate |r_{tj*}| > τ‖r_t‖₂
-- statement:
--   Let $\varepsilon,\delta>0$, $T,M\ge1$ with $\varepsilon\le T$, let $c_1$ be a Berry–Esseen constant (Theorem A.1), $\tau=\frac{\delta}{4c_1}\sqrt{\varepsilon/T}$ as in (7), and let the scale of the dictatorship test satisfy $\sigma\ge\frac1\delta\sqrt{\frac{8TM}{\pi\varepsilon}}$. Let $h(x)=\operatorname{sign}(r^{\mathsf T}x+c)$ with $r\in\mathbb R^{[T]\times[M]}$, $c\in\mathbb R$. Suppose there are distinct $s,t\in[T]$ with
--   $$0<\Big|\sum_{j=1}^M r_{sj}\Big|\le\Big|\sum_{j=1}^M r_{tj}\Big|\qquad\text{and}\qquad \mathrm{Acc}(h,\tilde D_s)>\tfrac12+\tfrac\delta2 .$$
--   Then there is $j^*\in[M]$ with
--   $$|r_{tj^*}|>\tau\|r_t\|_2 ,\qquad \|r_t\|_2=\Big(\sum_{j}r_{tj}^2\Big)^{1/2}.$$
--   This decodability property turns a classifier that does well on two tasks into a short list of candidate labels, which the NO case of the reduction uses.
--
--   Differences from the source:
--   - generalization: the test's scale σ = (1/δ)√(8TM/(πε)) of (7) → every σ ≥ (1/δ)√(8TM/(πε)); reason: the scale enters only through an upper bound on 1/σ in (13); equality is the paper's case
--   - reading: c_1 > 0 is the absolute constant from Theorem A.1 → any c₁ with IsBerryEsseenConstant c₁ (τ is computed from it); reason: the stronger reading: the lemma is claimed for every constant for which (5) holds, which is what its proof uses
--   - encoding: Dict(ε, δ, T, M) for ε > 0 → hypothesis ε ≤ T (with ε > 0); reason: the coordinate probabilities lie in [0, 1] only then; it excludes only parameters for which the test is undefined
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 18, Lemma A.7 (PDF p. 19)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Dataset
import Definitions.Def_ContinualHardness_Linear_Dict
import Definitions.Def_ContinualHardness_Linear_BerryEsseen

namespace ContinualHardness.Linear

/-- Lemma A.7 (decodability), p. 18. Let `h(x) = sign(rᵀx + c)`, let `c₁` be a Berry–Esseen
constant, `τ = (δ/(4c₁))√(ε/T)`, and let the scale of the test be at least
`σ = (1/δ)√(8TM/(πε))` of (7). If there are distinct blocks `s, t` with
`0 < |∑_j r_{sj}| ≤ |∑_j r_{tj}|` and `Acc(h, D̃_s) > 1/2 + δ/2`, then some coordinate satisfies
`|r_{tj*}| > τ‖r_t‖₂`. -/
theorem lemma_A_7 (ε δ c₁ σ : ℝ) (T M : ℕ) (hε : 0 < ε) (hεT : ε ≤ T) (hδ : 0 < δ)
    (hc₁ : IsBerryEsseenConstant c₁) (hσ : dictSigma ε δ T M ≤ σ)
    (r : Fin T × Fin M → ℝ) (c : ℝ) (s t : Fin T) (hst : s ≠ t)
    (hs : 0 < |∑ j : Fin M, r (s, j)|)
    (hst' : |∑ j : Fin M, r (s, j)| ≤ |∑ j : Fin M, r (t, j)|)
    (hacc : 1 / 2 + δ / 2 < acc (dictData ε σ T M s) (linClf r c)) :
    ∃ jstar : Fin M, dictTau c₁ ε δ T * blockNorm r t < |r (t, jstar)| := by sorry

end ContinualHardness.Linear
