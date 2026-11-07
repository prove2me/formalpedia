-- Prove2me | Theorems.Thm_DynHaussler_lemma_16
-- name    : DynHaussler.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:03.717809+00:00
-- url     : https://prove2.me/theorems/a5adaea6-39c5-4044-8363-98ffa14b6872
-- title:
--   Lemma 16 — partial SOA completion by at most $S_r(n)$ causal rules
-- statement:
--   Let $A\subseteq\{0,1,*\}^Z$ have Littlestone dimension at most $r\ge0$, and let $n\ge1$ be an integer. There is a family of at most
--   $$
--   S_r(n)=\sum_{i=0}^{\min\{r,n\}}\binom ni
--   $$
--   deterministic causal prediction rules $v=(v_t)_{t=1}^n$, with $v_t:Z^t\to\{0,1\}$, such that, on every sequence $z_1,\dots,z_k$ of length $k\le n$, each $\phi\in A$ is matched at all its defined positions by one rule: $v_t(z_{1:t})=\phi(z_t)$ whenever $\phi(z_t)\in\{0,1\}$.
--
--   The family is fixed before the sequence and the target; these rules are the finite family used in the double-sampling argument of Lemma 17.
--
--   **Formalization Note** A rule maps each round $t$ and prefix $z_{1:t}$ to a `Bool`; rounds are 0-based.
--
--   Differences from the source:
--   - encoding: rules v_t : Z^t → {0,1}, t = 1, …, n → (t : Fin n) → (Fin (t + 1) → Z) → Bool; reason: 0-based rounds; same rules
--   - encoding: Ldim with −1 for the empty class → partialLdim in ℕ∞ with 0 for the empty class; reason: "Ldim(A) ≤ r" for r ≥ 0 has the same meaning
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 16, pp.22–23 (PDF pp.24–25)

import Mathlib
import Definitions.Def_DynHaussler_partialLdim
import Definitions.Def_DynHaussler_sCount

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 16 (Partial SOA completion).** Let `A ⊆ {0,1,∗}^Z` have Littlestone dimension at most
`r ≥ 0`, and let `n ≥ 1` be an integer. There is a family of at most
`S_r(n) = ∑_{i=0}^{min{r,n}} binom(n, i)` deterministic causal prediction rules `v = (v_t)_{t=1}^n`,
with `v_t : Z^t → {0,1}`, such that, on every sequence of length at most `n`, each `ϕ ∈ A` is
matched at all its defined positions by one rule.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 16, pp.22–23 (PDF pp.24–25).

**Formalization Note** A rule is `(t : Fin n) → (Fin (t + 1) → Z) → Bool` (0-based rounds; the
value at round `t` reads `z_{1:t}`, the first `t + 1` entries). The family `v : Fin N → rule` is
fixed before the sequence `z : Fin k → Z` (`k ≤ n`) and the target `ϕ`; "matched at a defined
position `t`" means `ϕ(z_t) = some b → v_t(z_{1:t}) = b`. -/
theorem lemma_16 {Z : Type*} (A : Set (Z → Option Bool)) (r : ℕ) (hA : partialLdim A ≤ r)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (N : ℕ) (v : Fin N → (t : Fin n) → (Fin (t + 1) → Z) → Bool), N ≤ sCount r n ∧
      ∀ (k : ℕ) (hk : k ≤ n) (z : Fin k → Z), ∀ ϕ ∈ A, ∃ i : Fin N, ∀ t : Fin k, ∀ b : Bool,
        ϕ (z t) = some b →
          v i ⟨t, lt_of_lt_of_le t.isLt hk⟩ (fun j => z ⟨j, lt_of_lt_of_le j.isLt t.isLt⟩) = b := by sorry

end DynHaussler
