-- Prove2me | Theorems.Thm_AlmostMMS_lemma_5_1
-- name    : AlmostMMS.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:23.528258+00:00
-- url     : https://prove2.me/theorems/51f6b7fa-f6f5-4973-bbe2-2d648348330a
-- title:
--   Lemma 5.1 — supplier and recipients choice
-- statement:
--   Let $L_S\subseteq\{0,1,\dots,m\}$ be a set of $t$ protected prefixes. There is $U_0\subseteq U$ with
--   $$
--   |U_0|\ge\Big\lceil\frac{|U|}{(t+|S|+1)^{q^2}}\Big\rceil
--   $$
--   such that the following holds for every $u^*\in U_0$, every $J_0\subseteq[d]$ with $|J_0|\le|U_0|$, and every assignment of the profiles $\pi_{u^*,j}$, $j\in J_0$, to distinct agents $u(j)\in U_0$:
--   $$
--   \sum_{j\in J_0}P_{u(j)}(\pi^E_{u^*,j},\ell_s)=\sum_{j\in J_0}P_{u^*}(\pi^E_{u^*,j},\ell_s)\quad(\ell_s\in L_S),\qquad
--   \sum_{j\in J_0}P_{u(j)}(\pi^S_{u^*,j},\ell)\le|S\cap[\ell]|\quad(0\le\ell\le m).
--   $$
--   Within $U_0$ the agents are interchangeable for these constraints.
--
--   Differences from the source:
--   - reading: "a set U₀", with U and S from the context → U₀ ⊆ U for any given U and S; reason: the proof takes the largest group of U
--   - encoding: distinct agents u(j) ∈ U₀ → a function on Fin d, into U₀ and injective on J₀; reason: the same assignments
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Lemma 5.1, p.37

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_mmsProfileIn

namespace AlmostMMS

open Finset

/-- **Lemma 5.1 (Supplier and recipients choice), p.37.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `L_S ⊆ {0, …, m}` be a set of `t`
protected prefixes. There is `U₀` with `|U₀| ≥ ⌈|U|/(t + |S| + 1)^{q²}⌉` such that for any `u* ∈ U₀`, any
`J₀ ⊆ [d]` with `|J₀| ≤ |U₀|` and any assignment of the profiles `π_{u*,j}`, `j ∈ J₀`, to distinct agents
`u(j) ∈ U₀`, the protected loads of the `E`-parts are unchanged and
`∑_{j ∈ J₀} P_{u(j)}(π^S_{u*,j}, ℓ) ≤ |S ∩ [ℓ]|` for all `0 ≤ ℓ ≤ m`.

**Formalization Note.** `U₀ ⊆ U` is implicit on the page. Distinctness of the `u(j)` is injectivity on
`J₀`. The exponent is `q²`. -/
theorem lemma_5_1 {n m d q : ℕ} (hq : 3 ≤ q) (J : OrderedInstance n m d) (U : Finset (Fin n))
    (S : Finset (Fin m)) (LS : Finset ℕ) (hLS : LS ⊆ range (m + 1)) :
    ∃ U₀ ⊆ U,
      ⌈(U.card : ℝ) / ((LS.card : ℝ) + (S.card : ℝ) + 1) ^ (q ^ 2)⌉₊ ≤ U₀.card ∧
      ∀ u₀ ∈ U₀, ∀ (J₀ : Finset (Fin d)) (u : Fin d → Fin n), J₀.card ≤ U₀.card →
        (∀ j ∈ J₀, u j ∈ U₀) → Set.InjOn u (J₀ : Set (Fin d)) →
        (∀ ℓs ∈ LS, ∑ j ∈ J₀, load J.v (u j) (mmsProfileIn J q u₀ j Sᶜ) ℓs =
          ∑ j ∈ J₀, load J.v u₀ (mmsProfileIn J q u₀ j Sᶜ) ℓs) ∧
        ∀ ℓ ≤ m, ∑ j ∈ J₀, load J.v (u j) (mmsProfileIn J q u₀ j S) ℓ ≤ prefixCount S ℓ := by sorry

end AlmostMMS
