-- Prove2me | Theorems.Thm_FairTeamContracts_xos_support
-- name    : FairTeamContracts.xos_support
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:18.972346+00:00
-- url     : https://prove2.me/theorems/1350b18d-06d6-44f8-a1a1-0f2da74751b1
-- title:
--   §4.1 (proof of Proposition 4.3) — a supporting additive function of a submodular $f$ at $S$
-- statement:
--   Throughout, $f$ is a success function (monotone, $f(\emptyset)=0$, values in $[0,1]$) on the agents $N=[n]$, and the costs satisfy $c_i\ge0$.
--   Let $f$ be submodular and let $S\subseteq N$. There is an additive function $a$ with
--
--   1. $f(S)=\sum_{i\in S}a(i)=a(S)$;
--   2. $a(T)\le f(T)$ for every $T\subseteq S$;
--   3. $a(i)\ge f(i\mid S\setminus\{i\})$ for every $i\in S$;
--   4. $a(i)\ge0$ for every agent $i$.
--
--   This is the XOS property of submodular functions (Lehmann, Lehmann and Nisan, 2006), which the paper uses to replace a submodular instance by an additive one in the reduction of Proposition 4.3.
--
--   Differences from the source:
--   - generalization: an additive function a(·) with the three properties → additionally a(i) ≥ 0 for every agent i; reason: an extra true conclusion; it makes the additive instance of Proposition 4.3's proof a success function
--   - encoding: an additive function a(·), a(T) = Σ_{i∈T} a(i) → its singleton values a : Fin n → ℝ, with a(T) written as Σ_{i∈T} a i; reason: an additive function is determined by its singleton values
--   - encoding: submodular (Definition 2.4, for every i ∈ [n]) → published IsSubmodular (diminishing returns for e ∉ B) together with the monotonicity of IsSuccessFn; reason: Definition 2.4's extra cases i ∈ S′ only say a marginal is ≥ 0, which is monotonicity; same class of functions
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §4.1, proof of Proposition 4.3, p.14

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_marg

namespace FairTeamContracts

/-- **Supporting additive function of a submodular `f`** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §4.1, proof of
Proposition 4.3, p.14; the paper cites it from the XOS property of submodular functions,
Lehmann, Lehmann, Nisan 2006). For a submodular success function `f` and any set `S`, there is
an additive function `a` with `f(S) = ∑_{i∈S} a(i)`, `a(T) ≤ f(T)` for every `T ⊆ S`, and
`a(i) ≥ f(i | S∖{i})` for every `i ∈ S`; moreover `a` can be taken nonnegative.

**Formalization Note.** The additive function is given by its singleton values `a : Fin n → ℝ`,
with `a(T) = ∑_{i∈T} a i`. Nonnegativity of `a` is an extra conclusion (it is what makes the
additive instance of the proof a success function). -/
theorem xos_support {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : IsSuccessFn f) (hsub : SubsamplingSM.Offline.IsSubmodular f) (S : Finset (Fin n)) :
    ∃ a : Fin n → ℝ, ∑ i ∈ S, a i = f S ∧ (∀ T ⊆ S, ∑ i ∈ T, a i ≤ f T) ∧
      (∀ i ∈ S, marg f i S ≤ a i) ∧ ∀ i, 0 ≤ a i := by sorry

end FairTeamContracts
