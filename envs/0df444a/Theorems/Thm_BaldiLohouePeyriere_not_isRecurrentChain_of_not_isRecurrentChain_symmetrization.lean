-- Prove2me | Theorems.Thm_BaldiLohouePeyriere_not_isRecurrentChain_of_not_isRecurrentChain_symmetrization
-- name    : BaldiLohouePeyriere.not_isRecurrentChain_of_not_isRecurrentChain_symmetrization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:32:25.95569+00:00
-- url     : https://prove2.me/theorems/4b4c903a-1565-49d1-93b8-71a45595466d
-- title:
--   Lemma 5.5 (Baldi–Lohoué–Peyrière, external) — if the symmetrized walk is transient, so is the walk
-- statement:
--   Let a countable group $G$ act transitively on a set $X$, and let $\mu$ be a probability measure on $G$. Let $\nu = \frac12(\mu + \check\mu)$, where $\check\mu(g) = \mu(g^{-1})$. If the Markov chain on $X$ induced by $\nu$ (from $x$ to $g x$ with probability $\nu(g)$) is transient — from every starting point it fails to return with positive probability — then so is the chain induced by $\mu$.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 18: “Lemma 5.5 (Baldi, Lohoué and Peryère [BLP77]). Let $G$ be a countable group acting transitively on a set $X$ and $\mu$ be a probability measure on $G$. Consider the symmetric measure $\nu = \frac{1}{2}(\mu + \check\mu)$. Assume that the Markov chain on $X$ induced by $\nu$ is transient. Then so is the Markov chain induced by $\mu$.”
--
--   The measure $\mu$ need not be finitely supported; it is a nonnegative function on $G$ with total mass $1$.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 18, Lemma 5.5 (Baldi, Lohoué and Peyrière), which cites Baldi, P., Lohoué, N. and Peyrière, J., Sur la classification des groupes récurrents, C. R. Acad. Sci. Paris Sér. A–B 285 (1977) A1103–A1104 (no DOI), Proposition 1

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace BaldiLohouePeyriere

theorem not_isRecurrentChain_of_not_isRecurrentChain_symmetrization {G X : Type*} [Group G]
    [Countable G] [MulAction G X] [MulAction.IsPretransitive G X] (μ : G → ℝ)
    (hμ : (∀ g, 0 ≤ μ g) ∧ HasSum μ 1)
    (hν : ∀ x₀ : X, ¬ IsRecurrentChain (walkKernel fun g => (μ g + μ g⁻¹) / 2) x₀) :
    ∀ x₀ : X, ¬ IsRecurrentChain (walkKernel μ) x₀ := by
  sorry

end BaldiLohouePeyriere
