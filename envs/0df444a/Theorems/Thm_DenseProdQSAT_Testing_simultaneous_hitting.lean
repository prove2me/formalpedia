-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_simultaneous_hitting
-- name    : DenseProdQSAT.Testing.simultaneous_hitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:25.397206+00:00
-- url     : https://prove2.me/theorems/13ae78a3-4585-447a-b9e4-d39cd8781f80
-- title:
--   Lemma 3.2 — simultaneous hitting of historical bad sets
-- statement:
--   For each $k,d\ge2$ there exists a threshold $A_0>0$, independent of $\varepsilon,n,\Phi$, such that the following holds for every constant $A_{k,d}\ge A_0$ (the source's "let $A_{k,d}>0$ be sufficiently large"). For $0<\varepsilon\le1$ put $c=\lceil A_{k,d}\varepsilon^{-1}\log(2/\varepsilon)\rceil\ge1$. Suppose $n\ge c$ and choose $C$ uniformly among the $c$-subsets of $V$. For every instance, with probability at least $3/4$,
--
--   $$|R_i(A)|>\frac{\varepsilon n(|A|+1)}{128e^d}\quad\Longrightarrow\quad C\cap R_{i+1}(A)\ne\varnothing$$
--
--   holds simultaneously for every $i\in\{1,\ldots,J\}$ and every local assignment $A$ supported on $C$ with $|A|\le4e^d/\tau_i$. Here $J=\lceil\log_2(16/\varepsilon)\rceil$, $\tau_i=2^{-i}$, and $R_{J+1}$ keeps its historical Definition 2.5 meaning. No far-ness assumption is imposed. This is the joint hitting event used in the main theorem.
--
--   Differences from the source:
--   - encoding: tensor products on labels [n] and ordered supports → complex coordinate arrays on zero-based finite labels and lists of distinct labels; reason: canonical basis identification and relabeling preserve all assignments, dimensions, projectors and induced restrictions
--   - encoding: a sufficiently large unspecified A → a uniform threshold A₀ > 0 and the conclusion for every A ≥ A₀, with positive ceiling sample size; reason: "sufficiently large" means every A beyond some threshold depending only on k,d; c ≥ 1 holds for every A > 0 since log(2/ε) > 0
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Lemma 3.2, Eq. (2), p. 6

import Definitions.Def_DenseProdQSAT_Testing_Approximation
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem simultaneous_hitting (k d : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ (A : ℝ), A₀ ≤ A → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      1 ≤ SampleSize A ε ∧ ∀ (n : ℕ), 1 ≤ n → SampleSize A ε ≤ n →
      ∀ Φ : Instance n k d,
        3 / 4 ≤ SubsetProbability Finset.univ (SampleSize A ε) (fun C =>
          ∀ (i : ℕ), i ∈ Finset.Icc 1 (ScaleCount ε) →
          ∀ (F : List (Fin n)) (ψ : States n d), IsLocal Φ F ψ → F.toFinset ⊆ C →
            (F.length : ℝ) ≤ 4 * Real.exp d / Tau i →
            ε * n * (F.length + 1) / (128 * Real.exp d) < (BadSet Φ F ψ i).card →
            ¬ Disjoint C (BadSet Φ F ψ (i + 1))) := by sorry

end DenseProdQSAT.Testing
