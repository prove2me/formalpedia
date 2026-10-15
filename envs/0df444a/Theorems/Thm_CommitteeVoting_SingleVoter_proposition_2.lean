-- Prove2me | Theorems.Thm_CommitteeVoting_SingleVoter_proposition_2
-- name    : CommitteeVoting.SingleVoter.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:00:57.818754+00:00
-- url     : https://prove2.me/theorems/0041f566-3798-4de6-bae3-76740b9cd928
-- title:
--   Proposition 2, p. 20 — with one voter, approving the k candidates of highest posterior honesty is optimal
-- statement:
--   Consider $k$-winner approval voting (Definitions 1–3) with a single voter and $m \ge k$ candidates, tolerance $p \in [0,1]$, and let $s_1, \dots, s_m \in [0,1]$ be the voter's posterior probabilities that the candidates are honest. Let $\mathcal C^\star$ be any set of $k$ candidates with the highest posteriors, i.e. $|\mathcal C^\star| = k$ and $s_b \le s_a$ for all $a \in \mathcal C^\star$, $b \notin \mathcal C^\star$ (the cardinal strategy with $z = k$, Definition 6). Then for every ballot $\mathcal C$,
--
--   $$
--   \Pr[\mathbb T = H \mid s]\big|_{\text{ballot } \mathcal C} \;\le\; \Pr[\mathbb T = H \mid s]\big|_{\text{ballot } \mathcal C^\star},
--   $$
--
--   where $\mathbb T = H$ is the event that every committee the adversarial election rule of Definition 3 can produce has at least $\lceil (1-p)k \rceil$ honest members.
--
--   So a lone voter, or voters who pool their signals, cannot do better than approving exactly the $k$ candidates most likely to be honest: the cardinal strategy with $z = k$ is optimal among all strategies.
--
--   **Formalization Note** "Globally optimal strategy" is stated pointwise in the realised posteriors $s$ and for every ballot $\mathcal C$; since a strategy maps signals to ballots, pointwise optimality for every $s$ gives optimality of the expected success probability under any signal law, and the paper's proof (p. 45) argues pointwise as well. The Gaussian signal model (2)–(4) is not formalized. The ballot $\mathcal C$ is unrestricted in size (the cap $|\mathcal C| \le t$ of Definition 2 only shrinks the set of competitors, so the statement covers every $t$; Definition 6 needs $k \le t$ for $\mathcal C^\star$ to be allowed). The statement holds for every top-$k$ set, whatever the tie-breaking. $0 \le p \le 1$ is a standing assumption the paper leaves implicit (p is a tolerated fraction). The threshold is $\lceil (1-p)k \rceil$ as in Definition 3, not "$> (1-p)k$" as the proof on p. 45 writes. Indices are 0-based.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 20, Proposition 2; proof in Appendix B.2, p. 45

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial
import Definitions.Def_CommitteeVoting_SingleVoter_Committee
import Definitions.Def_CommitteeVoting_SingleVoter_SuccessProb

namespace CommitteeVoting.SingleVoter

/-- Proposition 2 (p. 20): with a single voter and `m ≥ k` candidates, approving any `k` candidates
of highest posterior probability of honesty (the cardinal strategy with `z = k`) maximises the
success probability `Pr[𝕋 = H | s]` over all ballots. -/
theorem proposition_2 {m k : ℕ} (hkm : k ≤ m) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Fin m → ℝ) (hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1)
    (Cstar : Finset (Fin m)) (hcard : Cstar.card = k)
    (htop : ∀ a ∈ Cstar, ∀ b ∉ Cstar, s b ≤ s a)
    (C : Finset (Fin m)) :
    successProb k p s C ≤ successProb k p s Cstar := by sorry

end CommitteeVoting.SingleVoter
