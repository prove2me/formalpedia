-- Prove2me | Theorems.Thm_Erdos195_max_rule_cascade
-- name    : Erdos195.max_rule_cascade
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:41:51.721983+00:00
-- url     : https://prove2.me/theorems/243324cf-aa85-46a8-9d04-c166e742740a
-- title:
--   The max-rule cascade $R_m$ never becomes tree-safe
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $P^*=(0,1,-1,-5)$. For $m\ge0$ let $w_j=2\cdot3^{j+1}-1$ and $R_m=(0,1,-1,5,3,2,w_1,\dots,w_m)$ (note $w_0=5$). Then every in-order $3$-AP $a,b,2b-a$ of $R_m$ has $3b-2a\in R_m$ before $2b-a$; the pairs $(1,-1)$ and $(-1,w_m)$ are open, at the same node $(1,\,1\bmod 2)$, with opposite bits; hence
--   $$R_m\ \text{is not tree-safe};$$
--   and the fourth term of $(-1,w_m)$ is $3w_m+2=w_{m+1}>\max R_m$. So the rule "close the conflict at the maximum by its fourth term" runs forever.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, `L <+: Q` means $L$ is a prefix of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem max_rule_cascade (m : ℕ) (R : List ℤ)
    (hR : R = [0, 1, -1, 5, 3, 2] ++ (List.range m).map (fun j : ℕ => (2 : ℤ) * 3 ^ (j + 2) - 1))
    (w : ℤ) (hw : w = 2 * 3 ^ (m + 1) - 1) :
    (∀ a b : ℤ, a ∈ R → b ∈ R → 2 * b - a ∈ R → R.idxOf a < R.idxOf b →
        R.idxOf b < R.idxOf (2 * b - a) →
        3 * b - 2 * a ∈ R ∧ R.idxOf (3 * b - 2 * a) < R.idxOf (2 * b - a)) ∧
    w ∈ R ∧ R.idxOf 1 < R.idxOf (-1) ∧ R.idxOf (-1) < R.idxOf w ∧
    2 * (-1) - 1 ∉ R ∧ 3 * (-1) - 2 * 1 ∉ R ∧ 2 * w - (-1) ∉ R ∧ 3 * w - 2 * (-1) ∉ R ∧
    padicValInt 2 (-1 - 1) = 1 ∧ padicValInt 2 (w - (-1)) = 1 ∧
    (1 : ℤ) % 2 ^ 1 = (-1) % 2 ^ 1 ∧ ¬ (bitOne (-1) 1 ↔ bitOne w 1) ∧
    (¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) R) ∧
    3 * w - 2 * (-1) = 2 * 3 ^ (m + 2) - 1 ∧ ∀ x ∈ R, x < 3 * w - 2 * (-1) := by sorry

end Erdos195
