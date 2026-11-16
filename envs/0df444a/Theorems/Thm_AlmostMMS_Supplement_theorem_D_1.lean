-- Prove2me | Theorems.Thm_AlmostMMS_Supplement_theorem_D_1
-- name    : AlmostMMS.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:30:28.425607+00:00
-- url     : https://prove2.me/theorems/857cb3a1-6d1d-4730-84db-f91ffc7f05d2
-- title:
--   Theorem D.1 — the single-supplier constant $C_{t,q}=\binom{t+q}{q}(t+1)q^t$
-- statement:
--   Let $t\ge1$ and $q\ge2$, and put
--   $$
--   C_{t,q}=\binom{t+q}{q}(t+1)\,q^t .
--   $$
--   Then Theorem C.1 (the single-supplier theorem, Theorem 5.1) holds with this constant. Precisely: take an ordered instance with $n$ agents, items $e_1,\dots,e_m$ and $d$ MMS bundles of value $1$ per agent; a set $S$ of items with complement $E=M-S$; a set $A$ of agents with $|A|\le d$ whose profiles $\pi_i$ have at most $q$ demands and fit in $E$ at the protected prefixes; an agent $u^*$ (the supplier) with MMS profiles $\pi^E_{u^*,j}$, $j\in[d]$; and a set $L_S\subseteq\{0,1,\dots,m\}$ of $t$ protected prefixes. There exist $A_0\subseteq A$ and $J_0\subseteq[d]$ with $|A_0|+|J_0|=d$ such that
--
--   1. $|J_0|\le C_{t,q}(d-|A|)$, and the number of added $E$-demands is $\sum_{j\in J_0}|\pi^E_{u^*,j}|\le q\,C_{t,q}(d-|A|)$;
--   2. for every protected prefix $\ell_s\in L_S$,
--   $$
--   \sum_{i\in A_0}P_i(\pi^E_i,\ell_s)+\sum_{j\in J_0}P_{u^*}(\pi^E_{u^*,j},\ell_s)\ \le\ |E\cap[\ell_s]| .
--   $$
--
--   Theorem 5.1 only asserts that some constant depending on $t$ and $q$ exists (via Dickson's lemma); this theorem makes it explicit, which is what gives the explicit $n_{\varepsilon,q}$ of Corollary D.1.
--
--   Differences from the source:
--   - reading: A from Theorem 4.1, the quantity d − |A|, and the global context for u*, E → explicit hypotheses |A| ≤ d, at most q demands per profile, and the fit at protected prefixes; reason: the proof of Theorem C.1 (pp.56–58) uses exactly these; for |A| > d the printed bound would be negative
--   - generalization: u* ∈ U and A the output of Theorem 4.1 → any agent u and any A with those properties; reason: the proof uses nothing else about them, and the source's data have the properties
--   - encoding: the standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: a family {π_i}_{i∈A} → a total function on agents read only on A; reason: values off A play no role
--   - generalization: Theorem C.1 under the standing q ≥ 3 of §§3–5 → every q ≥ 2, as Theorem D.1 prints; reason: D.1 asserts the constant for q ≥ 2, the proof of C.1 uses only |π| ≤ q, and at q ≥ 3 the statement is C.1 with this constant
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem D.1, p.59; Theorem C.1, p.55 (= Theorem 5.1, p.36)

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_mmsProfileIn

namespace AlmostMMS.Supplement

open Finset AlmostMMS

/-- **Theorem D.1, p.59.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC
2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…): for `t ≥ 1` and `q ≥ 2`, the constant
`C_{t,q}` in Theorem C.1 (= Theorem 5.1) can be chosen as `C_{t,q} = binom(t + q, q) (t + 1) q^t`.
That is, Theorem C.1 holds with this constant: for a supplier `u*` with MMS profiles `π_{u*,j}` and a
set `L_S ⊆ {0, …, m}` of `t` protected prefixes there are `A₀ ⊆ A` and `J₀ ⊆ [d]` with
`|A₀| + |J₀| = d`, `|J₀| ≤ C_{t,q}(d - |A|)`, `∑_{j ∈ J₀} |π^E_{u*,j}| ≤ q C_{t,q}(d - |A|)`, and
`∑_{i ∈ A₀} P_i(π^E_i, ℓs) + ∑_{j ∈ J₀} P_{u*}(π^E_{u*,j}, ℓs) ≤ |E ∩ [ℓs]|` at every `ℓs ∈ L_S`,
where `E = M - S`.

**Formalization Note.** The hypotheses on `A`, its profiles and `L_S` are those of the published
`AlmostMMS.theorem_5_1`: `|A| ≤ d`, profiles of at most `q` demands that fit in `E` at the protected
prefixes, any agent `u` as the supplier. `π^E_{u*,j}` is `mmsProfileIn J q u j Sᶜ`. Both clauses of
item 1 of Theorem C.1 are stated. -/
theorem theorem_D_1 (t q : ℕ) (ht : 1 ≤ t) (hq : 2 ≤ q) :
    ∀ {n m d : ℕ} (J : OrderedInstance n m d) (S : Finset (Fin m)) (A : Finset (Fin n))
      (π : Fin n → Multiset ℝ) (u : Fin n) (LS : Finset ℕ),
      LS ⊆ range (m + 1) → LS.card = t → A.card ≤ d → (∀ i ∈ A, (π i).card ≤ q) →
      (∀ ℓs ∈ LS, ∑ i ∈ A, load J.v i (π i) ℓs ≤ prefixCount Sᶜ ℓs) →
      ∃ A₀ ⊆ A, ∃ J₀ : Finset (Fin d), A₀.card + J₀.card = d ∧
        J₀.card ≤ Nat.choose (t + q) q * (t + 1) * q ^ t * (d - A.card) ∧
        ∑ j ∈ J₀, (mmsProfileIn J q u j Sᶜ).card ≤
          q * (Nat.choose (t + q) q * (t + 1) * q ^ t) * (d - A.card) ∧
        ∀ ℓs ∈ LS, ∑ i ∈ A₀, load J.v i (π i) ℓs +
          ∑ j ∈ J₀, load J.v u (mmsProfileIn J q u j Sᶜ) ℓs ≤ prefixCount Sᶜ ℓs := by sorry

end AlmostMMS.Supplement
