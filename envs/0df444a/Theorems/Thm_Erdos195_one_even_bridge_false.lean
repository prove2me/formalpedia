-- Prove2me | Theorems.Thm_Erdos195_one_even_bridge_false
-- name    : Erdos195.one_even_bridge_false
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T20:56:41.141917+00:00
-- url     : https://prove2.me/theorems/16699d89-265e-4df8-a8d5-41a34ff85ec5
-- title:
--   One-even bridge criterion with root bit 0: odd batches around a single new even letter
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework); its root bit $\theta(0,0)$ decides the order between integers of different parity ($\theta(0,0)=0$: every even integer precedes every odd integer at the root). A finite word $W$ of integers is $\theta$-safe if the sequence "letters of $W$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression. Write $W_{\mathrm{ev}}$, $W_{\mathrm{odd}}$ for the halved even and odd subwords ($x\mapsto\lfloor x/2\rfloor$), and $\theta^{(0)}(k,r)=\theta(k+1,2r)$, $\theta^{(1)}(k,r)=\theta(k+1,2r+1)$.
--
--   **Theorem (one-even bridge criterion, root bit 0).** Let $\theta(0,0)=0$. Let $S$ be a word that is safe for some tree witness with root bit $0$, let $P$ and $T$ be words of odd integers with $P\cap S=\emptyset$ and $T\cap(S\cup P)=\emptyset$, and let $y\notin S$ be even. Then $S\cdot P\cdot y\cdot T$ is $\theta$-safe if and only if
--   $$(S\cdot y)_{\mathrm{ev}}\ \text{is}\ \theta^{(0)}\text{-safe},\qquad (S\cdot P\cdot T)_{\mathrm{odd}}\ \text{is}\ \theta^{(1)}\text{-safe},$$
--   and the following root conditions hold:
--   1. for every even $a\in S$ and $b\in P$: $2b-a\in S$, or $3b-2a\in S\cup P$, or ($2b-a\neq y$ and $3b-2a\in T$);
--   2. for every even $a\in S\cup\{y\}$ and $b\in T$: $2b-a\in S\cup\{y\}$ or $3b-2a\in S\cup P\cup T$;
--   3. for every odd $a\in S\cup P$ with $2y-a\in T$: $3y-2a\in S$;
--   4. for odd $a$ before even $b$ in $S$ with $2b-a\in (P\cup T)\setminus S$: $3b-2a\in S$, or ($3b-2a=y$ and $2b-a\notin P$);
--   5. for even $a$ before odd $b$ in $S$ with $2b-a=y$: $3b-2a\in S\cup P$.
--
--   This is the root-bit-0 companion of the one-even bridge criterion (root bit 1). With root bit 0 every NEW odd letter that follows an old even letter (including $y$) must be closed by $2b-a$ or $3b-2a$ (conditions 1 and 2), whereas the even target $y$ itself needs no reflections, only condition 3 for odd letters reflected into the tail. After the odd shift $x\mapsto x+1$ (which flips the root bit and swaps parities), the case $T=\emptyset$ is the root-bit-1 exact lifting criterion for an even batch followed by an odd target; the tail $T$ is the new ingredient. Together with the root-bit-1 bridge, this gives exact criteria for both root bits.
--
--   Formalization note: words are `List ℤ`, membership/first-occurrence via `List.idxOf`, safety is `Safe (treeLt θ)`, halves via `filter`/`map (· / 2)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem one_even_bridge_false (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = false) (S P T : List ℤ) (y : ℤ)
    (hS : ∃ θS : ℕ → ℤ → Bool, θS 0 0 = false ∧ Safe (treeLt θS) S)
    (hPo : ∀ p ∈ P, p % 2 = 1) (hTo : ∀ t ∈ T, t % 2 = 1) (hy : y % 2 = 0) (hyS : y ∉ S)
    (hPS : ∀ p ∈ P, p ∉ S) (hTS : ∀ t ∈ T, t ∉ S ++ P) :
    Safe (treeLt θ) (S ++ P ++ [y] ++ T) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
        (((S ++ [y]).filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
        (((S ++ P ++ T).filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ a ∈ S, a % 2 = 0 → ∀ b ∈ P,
        2 * b - a ∈ S ∨ 3 * b - 2 * a ∈ S ++ P ∨ (2 * b - a ≠ y ∧ 3 * b - 2 * a ∈ T)) ∧
      (∀ a ∈ S ++ [y], a % 2 = 0 → ∀ b ∈ T,
        2 * b - a ∈ S ++ [y] ∨ 3 * b - 2 * a ∈ S ++ P ++ T) ∧
      (∀ a ∈ S ++ P, a % 2 = 1 → 2 * y - a ∈ T → 3 * y - 2 * a ∈ S) ∧
      (∀ a ∈ S, ∀ b ∈ S, a % 2 = 1 → b % 2 = 0 → S.idxOf a < S.idxOf b →
        2 * b - a ∉ S → 2 * b - a ∈ P ++ T →
        3 * b - 2 * a ∈ S ∨ (3 * b - 2 * a = y ∧ 2 * b - a ∉ P)) ∧
      (∀ a ∈ S, ∀ b ∈ S, a % 2 = 0 → b % 2 = 1 → S.idxOf a < S.idxOf b →
        2 * b - a = y → 3 * b - 2 * a ∈ S ++ P) := by sorry

end Erdos195
