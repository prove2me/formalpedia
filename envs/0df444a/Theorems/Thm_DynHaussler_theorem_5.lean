-- Prove2me | Theorems.Thm_DynHaussler_theorem_5
-- name    : DynHaussler.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:49.109619+00:00
-- url     : https://prove2.me/theorems/80666774-38e6-4997-a05e-e73c24b2ec99
-- title:
--   Theorem 5 — global dynamic $\ell_p$ upper bound $N^{\mathrm{dyn}}_p(F,\varepsilon,T)\le(C/\varepsilon^p)^{\mathrm{sfat}_{\varepsilon/32}(F)}$
-- statement:
--   There is a universal constant $C\ge1$ such that, for every $1\le p<\infty$, every integer $T\ge1$, every $0<\varepsilon<1/2$, and every nonempty $F\subseteq[0,1]^X$ with $d=\mathrm{sfat}_{\varepsilon/32}(F)<\infty$,
--   $$
--   N^{\mathrm{dyn}}_p(F,\varepsilon,T)\le\Bigl(\frac{C}{\varepsilon^p}\Bigr)^d. \tag{20}
--   $$
--   The constant $C$ is independent of $p,d,T,\varepsilon$ and the class. If $d=0$, the covering number is exactly one.
--
--   This is the upper half of the mission's goal; since $C\ge1$ and $p\ge1$ it gives $N^{\mathrm{dyn}}_p\le(C/\varepsilon)^{pd}$.
--
--   **Formalization Note** $C$ is chosen before every other parameter, including the domain $X$; "$d<\infty$" means $\mathrm{sfat}_{\varepsilon/32}(F)$ equals a natural number $d$.
--
--   Differences from the source:
--   - encoding: N^dyn_p ∈ ℕ ∪ {∞} compared with real numbers → dynCoverNum in ℕ∞, compared through ℕ∞ → ℝ≥0∞ with ENNReal.ofReal of the real bound; reason: same order on the nonnegative extended reals
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Theorem 5, Eq. (20), p.14 (PDF p.16); proof p.45 (PDF p.47)

import Mathlib
import Definitions.Def_DynHaussler_dynCoverNum
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

universe u

/-- **Theorem 5 (Global dynamic `ℓ_p` upper bound).** There is a universal constant `C ≥ 1` such that,
for every `1 ≤ p < ∞`, every integer `T ≥ 1`, every `0 < ε < 1/2`, and every nonempty `F ⊆ [0,1]^X`
with `d = sfat_{ε/32}(F) < ∞`, `N^dyn_p(F, ε, T) ≤ (C/ε^p)^d` (Eq. (20)). The constant `C` is
independent of `p, d, T, ε`, and the class. If `d = 0`, the covering number is exactly one.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Theorem 5, Eq. (20), p.14 (PDF p.16); proof p.45 (PDF p.47).

**Formalization Note** `C` is chosen before every other parameter, including the domain `X` (for
each universe level). "`d < ∞`" is `sfat_{ε/32}(F) = d` for a natural number `d`. `N^dyn_p` lies in
`ℕ∞` and is compared in `ℝ≥0∞`; `ε^p` is `Real.rpow`. The domain `X` is nonempty (the paper's
standing assumption, Section 3). -/
theorem theorem_5 :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (p : ℝ), 1 ≤ p → ∀ (T : ℕ), 1 ≤ T → ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (X : Type u) [Nonempty X] (F : Set (X → ℝ)), F.Nonempty →
        (∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
        ∀ d : ℕ, NondualOpt.sfat F (ε / 32) = d →
          ((dynCoverNum p ε F T : ℕ∞) : ENNReal) ≤ ENNReal.ofReal ((C / ε ^ p) ^ d) ∧
          (d = 0 → dynCoverNum p ε F T = 1) := by sorry

end DynHaussler
