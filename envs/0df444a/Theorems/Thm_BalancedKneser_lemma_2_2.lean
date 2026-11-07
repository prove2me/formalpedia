-- Prove2me | Theorems.Thm_BalancedKneser_lemma_2_2
-- name    : BalancedKneser.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:21.362684+00:00
-- url     : https://prove2.me/theorems/a8314454-8caf-4702-a250-5aaa4e801c80
-- title:
--   Lemma 2.2 — rejection families of monotone agents are exactly the independent families of $G_{n,c+1}$
-- statement:
--   Let $n>c\ge1$, let the goods be $[2n]$, and identify a balanced allocation with the $n$-set $A$ received by the first group (the second group receives $A^c$). For an agent with valuation $u$, her **rejection family** is the set of balanced allocations she rejects as EF$c$ (a first-group agent compares $A$ with $A^c$, a second-group agent compares $A^c$ with $A$). Then, for agents of either group:
--
--   1. A family $\mathcal F$ of balanced allocations is the rejection family of some agent with a monotone valuation if and only if $\mathcal F$ is an independent set of $G_{n,c+1}$, i.e. any two distinct members share at least $c+1$ elements.
--   2. Every independent family $\mathcal F$ of $G_{n,c+1}$ is the rejection family of an agent whose valuation $u$ is monotone, normalized ($u(\emptyset)=0$) and takes only the values $0$ and $1$.
--
--   This is the dictionary between fair division and coloring: a profile with no balanced EF$c$ allocation is exactly a covering of the vertices of $G_{n,c+1}$ by the agents' independent rejection families (Theorem 2.1).
--
--   **Formalization Note** Valuations are functions $\mathrm{Finset}(\mathrm{Fin}\,2n)\to\mathbb R$; monotone means $S\subseteq T\Rightarrow u(S)\le u(T)$. The two groups are stated as separate conjuncts.
--
--   Differences from the source:
--   - generalization: the rejection family of a monotone agent (§2: agents have normalized monotone valuations u : 2^M → ℝ≥0) → any monotone u : Finset (Fin (2n)) → ℝ in the if-and-only-if; reason: the forward direction (rejection family ⇒ independent) uses only monotonicity, and normalized nonnegative valuations are a special case; the backward direction is supplied with normalized 0/1 valuations by clauses 3–4
--   - encoding: goods M = [2n], balanced allocation = the n-set A of the first group → Fin (2 * n), vertices KSet (2 * n) n of G_{n,c+1}; reason: same instances
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Lemma 2.2, p.4 (PDF p.6); standing hypotheses n > c ≥ 1 and M = [2n] from §2 and Theorem 2.1, p.3

import Mathlib
import Definitions.Def_BalancedKneser_KG
import Definitions.Def_BalancedKneser_rejectionFamilyFirst

namespace BalancedKneser

/-- **Lemma 2.2** (Alipour–Jafari, *Balanced Fair Division and Generalized Kneser Graphs*,
arXiv:2611.04486v1, p.4 (PDF p.6)): "A family of balanced allocations is the rejection family of
a monotone agent if and only if it is independent in G_{n,c+1}. Every independent family is
realizable by a normalized 0/1-valued agent in either group."

Standing hypotheses (§2 and Theorem 2.1, p.3): goods `M = [2n]`, `n > c ≥ 1`; a balanced
allocation is the `n`-set `A` of the first group. Both groups are covered: a first-group agent
receives `A` (`rejectionFamilyFirst`), a second-group agent receives `Aᶜ`
(`rejectionFamilySecond`).

Formalization Note: in the "if and only if" the agent's valuation is any monotone
`u : Finset (Fin (2n)) → ℝ` (the source's agents are also normalized, `u ∅ = 0`; the forward
direction holds without it, and the backward direction is supplied by the realization clauses,
which produce normalized `{0,1}`-valued agents). -/
theorem lemma_2_2 (n c : ℕ) (hc : 1 ≤ c) (hcn : c < n) :
    (∀ F : Set (KSet (2 * n) n),
      (∃ u : Finset (Fin (2 * n)) → ℝ, Monotone u ∧ rejectionFamilyFirst c u = F) ↔
        (Gnr n (c + 1)).IsIndepSet F) ∧
    (∀ F : Set (KSet (2 * n) n),
      (∃ u : Finset (Fin (2 * n)) → ℝ, Monotone u ∧ rejectionFamilySecond c u = F) ↔
        (Gnr n (c + 1)).IsIndepSet F) ∧
    (∀ F : Set (KSet (2 * n) n), (Gnr n (c + 1)).IsIndepSet F →
      ∃ u : Finset (Fin (2 * n)) → ℝ, Monotone u ∧ u ∅ = 0 ∧ (∀ S, u S = 0 ∨ u S = 1) ∧
        rejectionFamilyFirst c u = F) ∧
    (∀ F : Set (KSet (2 * n) n), (Gnr n (c + 1)).IsIndepSet F →
      ∃ u : Finset (Fin (2 * n)) → ℝ, Monotone u ∧ u ∅ = 0 ∧ (∀ S, u S = 0 ∨ u S = 1) ∧
        rejectionFamilySecond c u = F) := by sorry

end BalancedKneser
