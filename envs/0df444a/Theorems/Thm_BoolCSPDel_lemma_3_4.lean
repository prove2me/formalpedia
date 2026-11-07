-- Prove2me | Theorems.Thm_BoolCSPDel_lemma_3_4
-- name    : BoolCSPDel.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:29.819159+00:00
-- url     : https://prove2.me/theorems/e0e021ec-9169-4e0f-9ef2-0278d36f8b67
-- title:
--   Lemma 3.4 — core pinning, for a relation and for a language
-- statement:
--   **For a relation.** If $R\subseteq\{0,1\}^a$ is a core, then for every variable set $V$ and assignment $\alpha:V\to\{0,1\}$ there are a set $Y$ of $4a$ variables disjoint from $V$ and an $R$-instance $P_\alpha$ on $V\cup Y$ with $O_k(|V|+1)$ constraints such that
--
--   $$\{\gamma|_V:\gamma\in\mathrm{Sat}_R(P_\alpha)\}=\{g\circ\alpha:g\in\mathrm{Aut}(R)\}.$$
--
--   Every scope has distinct variables and at least one from $Y$, no ordered scope is repeated, and if $R$ is symmetric no two scopes are permutations of each other.
--
--   **For a language.** When a language $\Gamma$ of nonempty relations is a core, any $\alpha$ on $V$ can be pinned up to one common automorphism, using constraints from $\Gamma$, with $O_k(|V|+1)$ constraints and $O_k(1)$ additional variables.
--
--   Pinning lets the reduction force a chosen assignment on the original variables.
--
--   Differences from the source:
--   - encoding: O_k(|V| + 1) and O_k(1), for a fixed R or Γ → constants C, Y chosen for k before the relation or language; reason: there are finitely many relations and languages of arity at most k (p.17)
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Lemma 3.4 and "Cores of constraint languages", p.19

import Mathlib
import Definitions.Def_BoolCSPDel_IsCore
import Definitions.Def_BoolCSPDel_fB

namespace BoolCSPDel

/-- **Lemma 3.4 (core pinning) and its form for languages.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Lemma 3.4 and the paragraph
"Cores of constraint languages", p.19.

First conjunct: for a core `R`, the scopes `P` on `V ∪ Y`, `|Y| = 4·arity`, with `O_k(|V| + 1)`
constraints, whose solutions restrict on `V` to exactly `{g ∘ α : g ∈ Aut(R)}`. Every scope has distinct
variables and at least one from `Y`; `P` is a `Finset`, so no ordered scope is repeated; for symmetric
`R`, no two scopes of `P` are permutations of each other. Second conjunct: the language form, with
`O_k(|V| + 1)` constraints and `O_k(1)` additional variables.

**Formalization Note.** The constants come before the relation, as the `O_k` of the page allow
(finitely many relations of arity at most `k`, p.17). -/
theorem lemma_3_4 (k : ℕ) : ∃ C Y : ℕ,
    (∀ R : Rel k, R.2.Nonempty → IsCore R → ∀ (V : Type) [Fintype V] (α : V → Bool),
      ∃ P : Finset (Fin R.1 → V ⊕ Fin (4 * R.1)),
        P.card ≤ C * (Fintype.card V + 1) ∧
        (∀ s ∈ P, Function.Injective s ∧ ∃ i, (s i).isRight) ∧
        {β | ∃ γ : V ⊕ Fin (4 * R.1) → Bool, (∀ s ∈ P, (γ ∘ s) ∈ R.2) ∧ β = γ ∘ Sum.inl} =
          {β | ∃ g, IsAut R g ∧ β = g ∘ α} ∧
        (IsSymmetric R → ∀ s ∈ P, ∀ s' ∈ P, (∃ π : Equiv.Perm (Fin R.1), s' = s ∘ π) → s = s')) ∧
    (∀ Γ : Lang k, (∀ R ∈ Γ, R.2.Nonempty) → IsCoreLang Γ →
      ∀ (V : Type) [Fintype V] (α : V → Bool),
        ∃ Q : Finset (Con Γ (V ⊕ Fin Y)), Q.card ≤ C * (Fintype.card V + 1) ∧ IsPinning Q α) := by sorry

end BoolCSPDel
