-- Prove2me | Theorems.Thm_FalconerPath_arzela_ascoli_profiles
-- name    : FalconerPath.arzela_ascoli_profiles
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:33.905821+00:00
-- url     : https://prove2.me/theorems/ef72e282-a9c6-4b9f-a96d-2fd63ce7d250
-- title:
--   Arzelà–Ascoli compactness for normalized scale profiles
-- statement:
--   Let $n\in\mathbb N$ and let $(m_j)_{j\ge0}$ be real-valued functions on $\mathbb R$ whose restrictions to $[0,1]$ are nondecreasing and $n$-Lipschitz, with $m_j(0)=0$ for every $j$. There are a strictly increasing map $\phi:\mathbb N\to\mathbb N$ and a real-valued function $m$ on $\mathbb R$ such that $m(0)=0$, $m$ is nondecreasing and $n$-Lipschitz on $[0,1]$, and $m_{\phi(j)}\to m$ uniformly on $[0,1]$. Explicitly, for every $\varepsilon>0$ there is $J$ such that $|m_{\phi(j)}(u)-m(u)|<\varepsilon$ for all $j\ge J$ and $u\in[0,1]$. Lean specializes the cited compactness theorem to these normalized profiles and leaves values outside $[0,1]$ unrestricted.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 2.3, Subpower losses and fixed gains, final compactness paragraph citing Folland1999, Theorem 4.43 (Arzelà–Ascoli). Used in Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale, proof paragraph beginning “We prove this assertion by contradiction”, at the passage to uniformly convergent profiles. This literature result has no separate numbered paper statement.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem arzela_ascoli_profiles (n : ℕ) (m : ℕ → ℝ → ℝ)
    (hzero : ∀ j, m j 0 = 0)
    (hmono : ∀ j, MonotoneOn (m j) (Icc 0 1))
    (hlip : ∀ j, LipschitzOnWith (Real.toNNReal n) (m j) (Icc 0 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ limit : ℝ → ℝ,
      limit 0 = 0 ∧ MonotoneOn limit (Icc 0 1) ∧
      LipschitzOnWith (Real.toNNReal n) limit (Icc 0 1) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ u ∈ Icc (0:ℝ) 1,
        |m (φ j) u-limit u| < ε := by sorry
end FalconerPath
