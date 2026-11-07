-- Prove2me | Theorems.Thm_AKSZigZag_section2_theorem_expanders_exist
-- name    : AKSZigZag.section2_theorem_expanders_exist
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:58.727489+00:00
-- url     : https://prove2.me/theorems/73877090-976f-44b2-9dc3-b54c0009606a
-- title:
--   §2 Theorem and Remark, p.4 — expanders with parameters $(\lambda,\alpha,c)$ exist for all $n$
-- statement:
--   Let $\lambda>1$ and $\alpha>0$ with $\lambda\alpha<1$. Then there is a number $c=c(\lambda,\alpha)$ such that for all $n$ there is an expander with parameters $(\lambda,\alpha,c)$ whose two sides have $n$ vertices each.
--
--   Moreover, there is such an expander whose sides have $n+1$ and $n$ vertices.
--
--   These are the paper's §2 Theorem and the Remark after it. Bounded-valency expanders are the only nonconstructive ingredient of the sorting network: §3 turns them into bounded-depth $\varepsilon$-halvers. The Remark's unequal sides are needed for odd $m$, where the halves have $\lceil m/2\rceil$ and $\lfloor m/2\rfloor$ registers.
--
--   Differences from the source:
--   - reading: sides |V₁| = |V₂| + 1 (Remark) with the bound |A| ≤ αn left unspecified → for unequal sides, |X| ≤ α·(size of the side containing Γ(X)); reason: for equal sides this is the paper's αn; bounding by the size of X's own side makes the claim false for small sides (λ = 1.98, α = 0.5, sides 2 and 1: a single vertex would need 1.98 neighbours among 1)
--   - encoding: c = c(λ,α) a real valency bound → c a natural number; reason: valencies are integers, so valency ≤ c is valency ≤ ⌊c⌋
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §2 Theorem and Remark, p.4

import Mathlib
import Definitions.Def_AKSZigZag_IsExpander

namespace AKSZigZag

/-- **Expanders exist** (AKS, STOC 1983, doi:10.1145/800061.808726, §2 Theorem and Remark, p.4):
"For any λ and α, λ > 1, α > 0, λα < 1, there is a c = c(λ,α) such that there are expander
graphs with parameters (λ,α,c) for all n. Remark. The condition |A| = |B| in the definition was
not essential, we will also use expanders with |A| = |B| + 1."

The valency bound `c` depends only on `λ` and `α`; the graph exists for sides of sizes `p, q`
with `p = q` (the Theorem) or `|p - q| = 1` (the Remark).

**Formalization Note.** For unequal sides, `IsExpander` bounds `|X|` by `α` times the size of the
side `Γ(X)` lies in; for `p = q = n` it is the paper's `|X| ≤ αn`. -/
theorem section2_theorem_expanders_exist (lam α : ℝ) (hlam : 1 < lam) (hα : 0 < α)
    (hlα : lam * α < 1) :
    ∃ c : ℕ, ∀ p q : ℕ, (p = q ∨ p = q + 1 ∨ q = p + 1) →
      ∃ E : Finset (Fin p × Fin q), IsExpander E lam α c := by sorry

end AKSZigZag
