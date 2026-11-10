-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_eq_9_1
-- name    : AlgCoverage.OddOrder.eq_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:37.917272+00:00
-- url     : https://prove2.me/theorems/527d2b8c-63fa-4ea5-91df-0fba4094c45e
-- title:
--   §9.1, Eq. (9.1) — translation averaging: $\mathbb E(F_{s+1}\mid F_s)=F_s^2$, $\mathbb EF_s^{2^{-s}}\le\mathbb EF_0$, $\Pr(F_s>0)\le N^{2^{-s}}\mathbb EF_0\le(1+o(1))e^{-\lambda_0+\ln N/2^s}$
-- statement:
--   Let $G$ be a finite group of odd order $N$ and let $F_s$ be the missing fraction $|G\setminus\mathcal W|/N$ after $s$ fresh iid uniform inputs are appended to a base list (in the paper the base list has length $k_0$). Appending a fresh input $g$ replaces the missing set by its intersection with the right translate by $g$, and
--
--   1. $\mathbb E(F_{s+1}\mid\text{past})=F_s^2$: for every input list $x$, $\frac1N\sum_{g\in G}F(x,g)=F(x)^2$;
--   2. $\mathbb EF_s^{2^{-s}}\le\mathbb EF_0$;
--   3. $\Pr(F_s>0)\le N^{2^{-s}}\mathbb EF_0$ (since $F_s>0$ forces $F_s\ge1/N$);
--   4. at the base length $k_0$, uniformly over odd-order groups and over $s$,
--   $$N^{2^{-s}}\mathbb EF_0\le(1+o(1))\exp\Big(-\lambda_0+\frac{\ln N}{2^s}\Big). \tag{9.1}$$
--
--   Together with (9.2) this gives the upper side of the median window.
--
--   Differences from the source:
--   - encoding: every finite group G of odd order → G : Type with [Group G] [Fintype G] and Odd (Fintype.card G); reason: every finite group is isomorphic to one in Type (universe 0), and every quantity in the statement is invariant under isomorphism
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
--   - encoding: sample length k₀ = ⌊c_N − 80⌋ → Int.toNat (k0 N), with λ₀ = (2^{k₀} − 1)/N computed with the integer power; reason: k₀ ≥ 1 for all large N, where the two agree; only eventual (N ≥ N₀) statements use the length
--   - generalization: base list of length k₀ → (1)–(3) for a base list of every length k; reason: they are exact statements valid for any initial list; k = k₀ is the specialization the paper uses, and (4) keeps k₀
--   - generalization: E(F_{s+1} | F_s) = F_s² → the average of F over the fresh input equals F² for every fixed past input list; reason: conditioning on the whole past implies the conditional identity given F_s by the tower property
--   - encoding: (1 + o(1)) in (9.1) → ∀ ε > 0, ∃ N₀, ∀ G odd with |G| ≥ N₀, ∀ s: … ≤ (1 + ε) exp(…); reason: one error function of N, uniform in the group and in s
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), pp. 27–28 (PDF 28–29), §9.1, Eq. (9.1)

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage

namespace AlgCoverage.OddOrder

/-- §9.1, Eq. (9.1) (upper side: translation averaging), Lin, printed pp. 27–28 / PDF 28–29. `G` of odd
order `N`, iid inputs, `F_s` the missing fraction after `s` fresh inputs are appended to a base list of
length `k` (in the paper `k = k₀`). (a) Appending a fresh uniform input `g` replaces the missing set by
its intersection with a right translate, and `E(F_{s+1} | past) = F_s²`; (b) `E F_s^{2^{−s}} ≤ E F_0`;
(c) `Pr(F_s > 0) ≤ N^{2^{−s}} E F_0`; (d) at the base length `k₀`, uniformly over odd-order groups and
`s`, `N^{2^{−s}} E F_0 ≤ (1 + o(1)) exp(−λ₀ + ln N / 2^s)`. -/
theorem eq_9_1 :
    (∀ (G : Type) [Group G] [Fintype G], Odd (Fintype.card G) →
      ∀ (k : ℕ) (x : Fin k → G),
        (∑ g : G, missingFrac (Fin.snoc (α := fun _ => G) x g)) / (Fintype.card G : ℝ) =
          (missingFrac x) ^ 2) ∧
    (∀ (G : Type) [Group G] [Fintype G], Odd (Fintype.card G) →
      ∀ k s : ℕ,
        expIid G (k + s) (fun x => (missingFrac x) ^ ((2 : ℝ) ^ (-(s : ℤ)))) ≤
          expIid G k (fun x => missingFrac x)) ∧
    (∀ (G : Type) [Group G] [Fintype G], Odd (Fintype.card G) →
      ∀ k s : ℕ,
        probIid G (k + s) (fun x => 0 < missingFrac x) ≤
          (Fintype.card G : ℝ) ^ ((2 : ℝ) ^ (-(s : ℤ))) * expIid G k (fun x => missingFrac x)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G → ∀ s : ℕ,
        (Fintype.card G : ℝ) ^ ((2 : ℝ) ^ (-(s : ℤ))) *
            expIid G (k0 (Fintype.card G)).toNat (fun x => missingFrac x) ≤
          (1 + ε) * Real.exp (-lam0 (Fintype.card G) +
            Real.log (Fintype.card G) / (2 : ℝ) ^ s)) := by sorry

end AlgCoverage.OddOrder
