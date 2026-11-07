-- Prove2me | Theorems.Thm_AlmostMMS_theorem_5_1
-- name    : AlmostMMS.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:22.806674+00:00
-- url     : https://prove2.me/theorems/3d1fd06b-2fa3-4095-8f8d-700079b68215
-- title:
--   Theorem 5.1 — single supplier
-- statement:
--   For every $t$ and $q\ge3$ there is a global constant $C_{t,q}$ such that the following holds. Let $u^*$ be an agent with MMS profiles $\{\pi_{u^*,j}:j\in[d]\}$, let $L_S\subseteq\{0,1,\dots,m\}$ be a set of $t$ protected prefixes, and let $A$ with $|A|\le d$ carry profiles of at most $q$ demands that fit in $E$ at the protected prefixes. There are $A_0\subseteq A$ and $J_0\subseteq[d]$ with $|A_0|+|J_0|=d$ and:
--
--   1. $|J_0|\le C_{t,q}(d-|A|)$;
--   2. for every $\ell_s\in L_S$,
--   $$
--   \sum_{i\in A_0}P_i(\pi^E_i,\ell_s)+\sum_{j\in J_0}P_{u^*}(\pi^E_{u^*,j},\ell_s)\le|E\cap[\ell_s]|.
--   $$
--   The constant depends only on $t$ and $q$, through Dickson's lemma, not on $n$, $m$, $d$ or the instance.
--
--   Differences from the source:
--   - reading: A from Theorem 4.1, the quantity d − |A|, and global context for u*, E → explicit hypotheses |A| ≤ d, at most q demands per profile, and the fit at protected prefixes; reason: the proof on pp.56–57 uses exactly these; for |A| > d the printed bound on |J₀| would be negative
--   - generalization: u* ∈ U and A the output of Theorem 4.1 → any agent u and any A with those properties; reason: the proof uses nothing else about them, and the source's data have the properties
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: a family {π_i}_{i∈I} → a total function on agents read only on I; reason: values off I play no role
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 5.1, p.36; Theorem C.1, p.55

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_mmsProfileIn

namespace AlmostMMS

open Finset

/-- **Theorem 5.1 (Single Supplier), p.36 (= Theorem C.1, p.55).** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): there is a global constant
`C_{t,q}` such that the following holds. For a supplier `u*` with MMS profiles `π_{u*,j}` and a set `L_S` of
`t` protected prefixes, there are `A₀ ⊆ A` and `J₀ ⊆ [d]` with `|A₀| + |J₀| = d`,
`|J₀| ≤ C_{t,q} (d - |A|)`, and `∑_{i ∈ A₀} P_i(π^E_i, ℓs) + ∑_{j ∈ J₀} P_{u*}(π^E_{u*,j}, ℓs) ≤ |E ∩ [ℓs]|`
at every `ℓs ∈ L_S`.

**Formalization Note.** `C` comes before the instance. The agents `A` with `|A| ≤ d`, and their profiles
of at most `q` demands that fit at the protected prefixes, are the only properties of Theorem 4.1's output
that the proof uses (pp.56–57), so the statement holds for any such data, and for any agent `u` as the
supplier. `|A| ≤ d` makes the natural subtraction the printed quantity. -/
theorem theorem_5_1 (t q : ℕ) (hq : 3 ≤ q) :
    ∃ C : ℕ, ∀ {n m d : ℕ} (J : OrderedInstance n m d) (S : Finset (Fin m)) (A : Finset (Fin n))
      (π : Fin n → Multiset ℝ) (u : Fin n) (LS : Finset ℕ),
      LS ⊆ range (m + 1) → LS.card = t → A.card ≤ d → (∀ i ∈ A, (π i).card ≤ q) →
      (∀ ℓs ∈ LS, ∑ i ∈ A, load J.v i (π i) ℓs ≤ prefixCount Sᶜ ℓs) →
      ∃ A₀ ⊆ A, ∃ J₀ : Finset (Fin d), A₀.card + J₀.card = d ∧ J₀.card ≤ C * (d - A.card) ∧
        ∀ ℓs ∈ LS, ∑ i ∈ A₀, load J.v i (π i) ℓs +
          ∑ j ∈ J₀, load J.v u (mmsProfileIn J q u j Sᶜ) ℓs ≤ prefixCount Sᶜ ℓs := by sorry

end AlmostMMS
