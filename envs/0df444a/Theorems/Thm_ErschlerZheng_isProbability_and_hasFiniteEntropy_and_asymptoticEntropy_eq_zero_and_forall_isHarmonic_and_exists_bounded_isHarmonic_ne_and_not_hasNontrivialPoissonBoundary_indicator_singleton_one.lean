-- Prove2me | Theorems.Thm_ErschlerZheng_isProbability_and_hasFiniteEntropy_and_asymptoticEntropy_eq_zero_and_forall_isHarmonic_and_exists_bounded_isHarmonic_ne_and_not_hasNontrivialPoissonBoundary_indicator_singleton_one
-- name    : ErschlerZheng.isProbability_and_hasFiniteEntropy_and_asymptoticEntropy_eq_zero_and_forall_isHarmonic_and_exists_bounded_isHarmonic_ne_and_not_hasNontrivialPoissonBoundary_indicator_singleton_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:14:58.157321+00:00
-- url     : https://prove2.me/theorems/741763ff-72f8-49c2-894c-133c15944e83
-- title:
--   p. 10, read literally, fails at δ_id — on a non-trivial group δ_id has finite entropy and h = 0, yet every function is δ_id-harmonic; its Poisson boundary as defined here is trivial
-- statement:
--   Let $G$ be a non-trivial group (`Nontrivial G`) and $\delta_{id}$ the point mass at its identity, written `Set.indicator {1} 1`: $\delta_{id}(1) = 1$ and $\delta_{id}(g) = 0$ for $g \ne 1$. Then $\delta_{id}$ is a probability (`IsProbability`) of finite entropy (`HasFiniteEntropy`) whose asymptotic entropy $\mathbf h_{\delta_{id}}$ (`asymptoticEntropy`) is $0$; every function $f : G \to \mathbb R$ is $\delta_{id}$-harmonic (`IsHarmonic`); there is a bounded $\delta_{id}$-harmonic function $f : G \to \mathbb R$, $|f(x)| \le C$ for all $x$, with $f(x) \ne f(y)$ for some $x, y \in G$; and the Poisson boundary of $(G, \delta_{id})$ is trivial, `¬ HasNontrivialPoissonBoundary`.
--
--   This is not a result of the paper. It backs the sentences of the Walks bundle note `ErschlerZheng_Walks` on $\delta_{id}$: read literally for every $\mu$, the criterion of p. 2 would make the boundary of $\delta_{id}$ non-trivial on any non-trivial group, since every function is $\delta_{id}$-harmonic, while $\delta_{id}$ has asymptotic entropy $0$; and the definition `HasNontrivialPoissonBoundary` gives $\delta_{id}$ a trivial boundary. It also backs the last sentence of the note on `KaimanovichVershik.not_hasNontrivialPoissonBoundary_iff_asymptoticEntropy_eq_zero`: for the point mass at the identity of a non-trivial group, $\mathbf h_\mu = 0$, yet every function is harmonic, so the quoted equivalence of p. 10 fails when read literally for every $\mu$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 10, the point mass at the identity (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Walks

namespace ErschlerZheng

theorem isProbability_and_hasFiniteEntropy_and_asymptoticEntropy_eq_zero_and_forall_isHarmonic_and_exists_bounded_isHarmonic_ne_and_not_hasNontrivialPoissonBoundary_indicator_singleton_one
    {G : Type*} [Group G] [Nontrivial G] :
    IsProbability (Set.indicator {1} 1 : G → ℝ) ∧ HasFiniteEntropy (Set.indicator {1} 1 : G → ℝ) ∧
      asymptoticEntropy (Set.indicator {1} 1 : G → ℝ) = 0 ∧
      (∀ f : G → ℝ, IsHarmonic (Set.indicator {1} 1) f) ∧
      (∃ f : G → ℝ, (∃ C, ∀ x, |f x| ≤ C) ∧ IsHarmonic (Set.indicator {1} 1) f ∧
        ∃ x y, f x ≠ f y) ∧
      ¬ HasNontrivialPoissonBoundary (Set.indicator {1} 1 : G → ℝ) := by
  sorry

end ErschlerZheng
