-- Prove2me | Theorems.Thm_DynHaussler_proposition_2
-- name    : DynHaussler.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:32.558201+00:00
-- url     : https://prove2.me/theorems/3a56163b-3102-4fe7-8fd4-9bd3700dce90
-- title:
--   Proposition 2 — global outlier cover by at most $(C_0R)^d$ causal experts
-- statement:
--   There is a universal constant $C_0\ge1$ with the following property. Let $d\ge0$ be an integer, $0<\eta<1$, $R>32$, $T\ge1$, and let $\emptyset\neq H\subseteq[0,1]^X$ satisfy $\mathrm{sfat}_\eta(H)\le d<\infty$ and $\|h-h'\|_\infty>\eta$ for distinct $h,h'\in H$. There is a family $G$ of at most $(C_0R)^d$ deterministic causal experts such that, for every instance sequence $x_{1:T}$ and every $h\in H$, some $g\in G$ satisfies
--   $$
--   \#\{t\in[T]:\ |g_t(x_{1:t})-h(x_t)|\ge8\eta\}<\frac{T}{8R}. \tag{8}
--   $$
--   The family is fixed independently of the instance sequence.
--
--   The proposition allows a small fraction of outlier rounds with larger error; together with Lemma 9 and the calculation (9) it yields the horizon-independent upper bound of Theorem 5.
--
--   **Formalization Note** $C_0$ is chosen before every other parameter, including the domain; the family is indexed by $\{0,\dots,k-1\}$ with $k\le(C_0R)^d$ and is chosen before the sequence.
--
--   Differences from the source:
--   - encoding: ‖h − h′‖∞ > η and ‖f − h‖∞ ≤ η → ∃ x, η < |h x − h′ x| and ∀ x, |f x − h x| ≤ η; reason: a supremum exceeds η exactly when some term does, and is at most η exactly when every term is
--   - encoding: rounds 1, …, T and prefixes x_{1:t} → rounds Fin T (0-based); round t reads the first t + 1 instances; reason: index shift only
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Proposition 2, Eq. (8), p.6 (PDF p.8); proof p.44 (PDF p.46)

import Mathlib
import Definitions.Def_DynHaussler_CausalExpert
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

universe u

/-- **Proposition 2 (Global outlier cover).** There is a universal constant `C_0 ≥ 1` with the
following property. Let `d ≥ 0` be an integer, `0 < η < 1`, `R > 32`, `T ≥ 1`, and let
`∅ ≠ H ⊆ [0,1]^X` satisfy `sfat_η(H) ≤ d < ∞` and `‖h − h'‖_∞ > η` for distinct `h, h' ∈ H`. There is a
family `G` of at most `(C_0 R)^d` deterministic causal experts such that, for every instance sequence
`x_{1:T}` and every `h ∈ H`, some `g ∈ G` satisfies `#{t ∈ [T] : |g_t(x_{1:t}) − h(x_t)| ≥ 8η} < T/(8R)`
(Eq. (8)). The family is fixed independently of the instance sequence.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Proposition 2, Eq. (8), p.6 (PDF p.8); proof p.44 (PDF p.46).

**Formalization Note** `C_0` is chosen before every other parameter, including the domain `X`
(for each universe level). The family is `G : Fin k → CausalExpert X T` with `k ≤ (C_0 R)^d`, chosen
before the instance sequence. `‖h − h'‖_∞ > η` is `∃ x, η < |h x − h' x|`. Rounds are 0-based. The
domain `X` is nonempty (the paper's standing assumption, Section 3). -/
theorem proposition_2 :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ (d : ℕ) (η R : ℝ) (T : ℕ), 0 < η → η < 1 → 32 < R → 1 ≤ T →
      ∀ (X : Type u) [Nonempty X] (H : Set (X → ℝ)), H.Nonempty →
        (∀ h ∈ H, ∀ x, h x ∈ Set.Icc (0 : ℝ) 1) → NondualOpt.sfat H η ≤ d →
        (∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∃ x, η < |h x - h' x|) →
        ∃ (k : ℕ) (G : Fin k → CausalExpert X T), (k : ℝ) ≤ (C₀ * R) ^ d ∧
          ∀ x : Fin T → X, ∀ h ∈ H, ∃ i : Fin k,
            ((Finset.univ.filter (fun t => 8 * η ≤ |(G i).run x t - h (x t)|)).card : ℝ)
              < T / (8 * R) := by sorry

end DynHaussler
