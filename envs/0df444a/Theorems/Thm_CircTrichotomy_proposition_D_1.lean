-- Prove2me | Theorems.Thm_CircTrichotomy_proposition_D_1
-- name    : CircTrichotomy.proposition_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:46.356174+00:00
-- url     : https://prove2.me/theorems/87ed1cc6-6c17-4c10-825b-34ad49171219
-- title:
--   Proposition D.1 — stamps in $\mathbf X$ are constant on $\simeq_k$-classes, $k=4s(N+1)!$
-- statement:
--   **Proposition D.1.** Let $\varphi:\Sigma^+\to S$ be a stamp in $\mathbf X$ with stability index $s$, let $N=|\mathrm{stab}(\varphi)|$ and $k=4s(N+1)!$. For all $u,v\in\Sigma^+$,
--   $$u\simeq_k v\implies\varphi(u)=\varphi(v).$$
--
--   It gives the direction (4) ⇒ (5) of Theorem 2.8.
--
--   Differences from the source:
--   - encoding: a stamp φ : Σ⁺ → S → a MulHom φ : FreeSemigroup α →ₙ* S with IsStamp φ (surjective, S finite); reason: FreeSemigroup α is Σ⁺ with concatenation
--   - encoding: the ω-powers in the identities (1) of X → any e, f with IsOmegaPow (idempotent positive powers); reason: in a finite semigroup (S(L) for regular L, S for a stamp) there is exactly one such element, the ω-power
--   - encoding: N = |stab(φ)| → Set.ncard (lenImage φ s); reason: stab(φ) = φ(Σˢ) is a subset of the finite semigroup S
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Proposition D.1, p.47

import Mathlib
import Definitions.Def_CircTrichotomy_wordToList
import Definitions.Def_CircTrichotomy_IsStamp
import Definitions.Def_CircTrichotomy_IsStabilityIndex
import Definitions.Def_CircTrichotomy_InX
import Definitions.Def_CircTrichotomy_simeqTD

set_option autoImplicit false

namespace CircTrichotomy

/-- **Proposition D.1** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Proposition D.1, p.47): "Let φ be a stamp in X with stability index s.
Let N = |stab(φ)| and k = 4s(N + 1)!. For each u, v ∈ Σ⁺ we have that if u ≃_k v, then
φ(u) = φ(v)."

**Formalization Note** `stab(φ) = φ(Σˢ)` is `lenImage φ s` and `N` its cardinality (a finite set,
since `S` is finite). `≃_k` is `simeqK k` on the underlying lists. -/
theorem proposition_D_1 {α S : Type} [Fintype α] [Nonempty α] [Semigroup S]
    (φ : FreeSemigroup α →ₙ* S) (hφ : IsStamp φ) (hX : InX φ) (s : ℕ)
    (hs : IsStabilityIndex φ s) :
    ∀ u v : FreeSemigroup α,
      simeqK (4 * s * (Set.ncard (lenImage φ s) + 1).factorial) (wordToList u) (wordToList v) →
        φ u = φ v := by sorry

end CircTrichotomy
