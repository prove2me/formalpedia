-- Prove2me | Theorems.Thm_AlmostMMS_corollary_5_1
-- name    : AlmostMMS.corollary_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:53.695203+00:00
-- url     : https://prove2.me/theorems/47636705-8bc0-4d0e-8468-ed0d7fbb38bd
-- title:
--   Corollary 5.1 — completing the selection from one supplier
-- statement:
--   For every fixed $\varepsilon\in(0,1)$ and integer $q\ge3$ there is $n_{\varepsilon,q}$ such that the following holds for every $n\ge n_{\varepsilon,q}$, $1\le d\le(1-\varepsilon)n$, and ordered instance with $\overline T<\rho_{q,n}/\gamma$. There are a set $S$ of items and a partition $N=U+V+W$ with $|V|\ge d$, $|U|=\lfloor\varepsilon n/8\rfloor$ and $h_v\le h_u$ for $u\in U$, $v\in V$, such that for every output $A\subseteq V$ of Theorem 4.1, with profiles $\pi_i$, $|A|<d$ implies the following. There is a nonempty $U_0\subseteq U$ such that for any $u^*\in U_0$ one can choose $A_0\subseteq A$, $J_0\subseteq[d]$ with $|J_0|\le|U_0|$ and $|A_0|+|J_0|=d$, and distinct $u(j)\in U_0$, so that for all $0\le\ell\le m$
--   $$
--   \sum_{i\in A_0}P_i(\pi_i,\ell)+\sum_{j\in J_0}P_{u(j)}(\pi_{u^*,j},\ell)\le\ell,
--   $$
--   $$
--   \sum_{i\in A_0}P_i(\pi_i,\ell)+\sum_{j\in J_0}P_{u^*}(\pi^E_{u^*,j},\ell)\le|E\cap[\ell]|,\qquad\sum_{j\in J_0}P_{u^*}(\pi^S_{u^*,j},\ell)\le|S\cap[\ell]|.
--   $$
--
--   Differences from the source:
--   - reading: S, U, V, W left to the context (Definition 4.2; "according to Corollary 5.1", p.43) → existential, before A, with the properties of Lemma 4.1 and Definition 4.2 that are later used (|W| ≤ εn/8, the partition, |V| ≥ d, |U| = ⌊εn/8⌋, largest heads in U); reason: the page's statement names them without defining them
--   - generalization: "Let A ⊆ V be the assigned agents from Theorem 4.1" (one output) → every output (A, j) of Theorem 4.1 for (S, V); reason: the proof uses only the three bullets of Theorem 4.1, so it applies to each output; one output is a special case
--   - generalization: the last two displayed bounds are not in the corollary → stated in the conclusion; reason: they are (E) and (S) in the proof of Observation 5.1, p.41, which Theorem 5.2 needs; the printed conclusion is kept as well
--   - generalization: "there exists a choice of U₀" → U₀ is also nonempty; reason: without it the ∀ u* could be empty; the proof gives |U₀| ≥ C_q(d − |A|) ≥ 1
--   - encoding: the lambda (1 − 1/(2q))⁻¹ → the same `lambdaQ q` as 2q/(2q − 1); reason: equal numbers
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: choices j_i for i ∈ A → a total function j : Fin n → Fin d read only on A; reason: values off A play no role
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Corollary 5.1, p.39; Definition 4.2, p.34; proof of Observation 5.1, p.41

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_mmsProfileIn
import Definitions.Def_AlmostMMS_rhoQN
import Definitions.Def_AlmostMMS_IsPartialSelection

namespace AlmostMMS

open Finset

/-- **Corollary 5.1, p.39.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): for every fixed `ε ∈ (0, 1)` and integer `q ≥ 3` there is `n_{ε,q}` such
that for `n ≥ n_{ε,q}`, if `T̄ < ρ_{q,n}/γ`, then: for `A ⊆ V` the agents from Theorem 4.1 with profiles `π_i`,
if `|A| < d`, there is `U₀ ⊆ U` such that for any `u* ∈ U₀` one can choose `A₀ ⊆ A` and `J₀ ⊆ [d]` with
`|J₀| ≤ |U₀|`, `|A₀| + |J₀| = d`, and distinct `u(j) ∈ U₀` with
`∑_{i ∈ A₀} P_i(π_i, ℓ) + ∑_{j ∈ J₀} P_{u(j)}(π_{u*,j}, ℓ) ≤ ℓ` for all `0 ≤ ℓ ≤ m`.

**Formalization Note.** The page leaves `S, U, V, W` to its context (Definition 4.2; "construct partitions
… according to Corollary 5.1", p.43), so they are existential, before `A`: `(U, V, W)` partitions `N`,
`|W| ≤ εn/8` (Lemma 4.1), `|V| ≥ d`, `|U| = ⌊εn/8⌋` and `h_v ≤ h_u` for `u ∈ U`, `v ∈ V`. The claim is for every output `(A, j)` of
Theorem 4.1. Three clauses are added: `U₀` is nonempty, without which the `∀ u*` would be empty (the proof
has `|U₀| ≥ C_q (d - |A|) ≥ 1`, and Theorem 5.2 picks `u*` from `U₀`); and the two bounds of the proof of
Observation 5.1 (p.41) on the `E`-load and the `S`-load of the supplier's own copies. -/
theorem corollary_5_1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (q : ℕ) (hq : 3 ≤ q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (m d : ℕ) (J : OrderedInstance n m d), 1 ≤ d →
      (d : ℝ) ≤ (1 - ε) * (n : ℝ) → avgTail J.v q < rhoQN q d n / gammaQ ε q →
      ∃ (S : Finset (Fin m)) (U V W : Finset (Fin n)),
        Disjoint U V ∧ Disjoint U W ∧ Disjoint V W ∧ U ∪ V ∪ W = univ ∧
        (W.card : ℝ) ≤ ε * (n : ℝ) / 8 ∧ d ≤ V.card ∧ U.card = ⌊ε * (n : ℝ) / 8⌋₊ ∧
        (∀ u ∈ U, ∀ w ∈ V, headCount J.v q w ≤ headCount J.v q u) ∧
        ∀ (A : Finset (Fin n)) (j : Fin n → Fin d), IsPartialSelection J q S V A j → A.card < d →
          ∃ U₀ ⊆ U, U₀.Nonempty ∧ ∀ u₀ ∈ U₀, ∃ A₀ ⊆ A, ∃ (J₀ : Finset (Fin d)) (u : Fin d → Fin n),
            J₀.card ≤ U₀.card ∧ A₀.card + J₀.card = d ∧ (∀ k ∈ J₀, u k ∈ U₀) ∧
            Set.InjOn u (J₀ : Set (Fin d)) ∧
            (∀ ℓ ≤ m, ∑ i ∈ A₀, load J.v i (mmsProfile J q i (j i)) ℓ +
              ∑ k ∈ J₀, load J.v (u k) (mmsProfile J q u₀ k) ℓ ≤ ℓ) ∧
            (∀ ℓ ≤ m, ∑ i ∈ A₀, load J.v i (mmsProfile J q i (j i)) ℓ +
              ∑ k ∈ J₀, load J.v u₀ (mmsProfileIn J q u₀ k Sᶜ) ℓ ≤ prefixCount Sᶜ ℓ) ∧
            (∀ ℓ ≤ m, ∑ k ∈ J₀, load J.v u₀ (mmsProfileIn J q u₀ k S) ℓ ≤ prefixCount S ℓ) := by sorry

end AlmostMMS
