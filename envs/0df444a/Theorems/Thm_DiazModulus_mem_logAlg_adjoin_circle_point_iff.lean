-- Prove2me | Theorems.Thm_DiazModulus_mem_logAlg_adjoin_circle_point_iff
-- name    : DiazModulus.mem_logAlg_adjoin_circle_point_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T17:47:46.061557+00:00
-- url     : https://prove2.me/theorems/fd55e4d6-c196-4201-a0a2-95fbe06faf50
-- title:
--   For every u ∈ ℂ, z lies in span_ℚ ℒ + ℚu + ℚū exactly when z = c + pu + qū with c ∈ ℒ and p, q ∈ ℚ, and the Q̄-span of 1 and this space is ℒ̃ + Q̄u + Q̄ū
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers (the $z \in \mathbb{C}$ with $e^z$ algebraic), and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$. Let $u \in \mathbb{C}$ be arbitrary and $\mathcal{L}_u = \mathrm{span}_{\mathbb{Q}}(\mathcal{L}) + \mathrm{span}_{\mathbb{Q}}(u, \bar u)$. Then:
--
--   - $z \in \mathcal{L}_u$ if and only if $z = c + pu + q\bar u$ for some $c \in \mathcal{L}$ and $p, q \in \mathbb{Q}$;
--   - $\mathrm{span}_{\overline{\mathbb{Q}}}(\{1\} \cup \mathcal{L}_u) = \widetilde{\mathcal{L}} + \mathrm{span}_{\overline{\mathbb{Q}}}(u, \bar u)$.
--
--   **Proof.** $\mathcal{L}$ is already a $\mathbb{Q}$-subspace of $\mathbb{C}$: it contains $0$, it is closed under addition since $e^{a+b} = e^ae^b$, and under rational multiples by `Diaz.exp_ratMul_isAlgebraic`; so by span induction $\mathrm{span}_{\mathbb{Q}}(\mathcal{L}) \subseteq \mathcal{L}$, and membership in the sum unfolds to $z = c + pu + q\bar u$. For the second part, $1$ and every $c + pu + q\bar u$ lie in $\widetilde{\mathcal{L}} + \mathrm{span}_{\overline{\mathbb{Q}}}(u, \bar u)$, as rationals are algebraic. Conversely $\widetilde{\mathcal{L}} = \mathrm{span}_{\overline{\mathbb{Q}}}(\{1\} \cup \mathcal{L})$ lies in $\mathrm{span}_{\overline{\mathbb{Q}}}(\{1\} \cup \mathcal{L}_u)$ because $\mathcal{L} \subseteq \mathcal{L}_u$, and so do $u$ and $\bar u$, which lie in $\mathcal{L}_u$.
--
--   **Novelty.** Elementary; routine.
-- source:
--   Elementary. Uses Diaz.exp_ratMul_isAlgebraic. R19 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem mem_logAlg_adjoin_circle_point_iff
    (u : ℂ) :
    (∀ z : ℂ, z ∈ (Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ)) ↔
      ∃ c ∈ LogAlg, ∃ p q : ℚ, z = c + (p : ℂ) * u + (q : ℂ) * conj u) ∧
    Submodule.span Qbar (insert 1 ((Submodule.span ℚ LogAlg ⊔ Submodule.span ℚ ({u, conj u} : Set ℂ) : Submodule ℚ ℂ) : Set ℂ)) =
      LogAlgTilde ⊔ Submodule.span Qbar ({u, conj u} : Set ℂ) := by
  sorry

end DiazModulus
