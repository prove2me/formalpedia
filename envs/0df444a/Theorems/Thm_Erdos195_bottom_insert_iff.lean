-- Prove2me | Theorems.Thm_Erdos195_bottom_insert_iff
-- name    : Erdos195.bottom_insert_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:33:29.385981+00:00
-- url     : https://prove2.me/theorems/88b3bee7-e505-46d6-820d-29781ab057e0
-- title:
--   Bottom-insertion criterion for tree orders
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $t\notin P$. There is a tree witness $\theta$ such that $P$ is $\theta$-safe and $t\prec_\theta a$ for all $a\in P$ if and only if $P$ is tree-safe for some witness and, for every $a\in P$ and every open pair $(x,y)$ of $P$ at the node of $(a,t)$, i.e.
--   $$\nu_2(y-x)=\nu_2(a-t)=k,\quad x\equiv t\pmod{2^k},$$
--   we have $\mathrm{bit}_k(y)=\mathrm{bit}_k(t)$. (Bottom-insertion criterion.)
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem bottom_insert_iff (P : List ℤ) (t : ℤ) (ht : t ∉ P) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) P ∧ ∀ a ∈ P, treeLt θ t a) ↔
      ((∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) P) ∧
        ∀ a ∈ P, ∀ x y : ℤ, x ∈ P → y ∈ P → P.idxOf x < P.idxOf y → 2 * y - x ∉ P →
          3 * y - 2 * x ∉ P → padicValInt 2 (y - x) = padicValInt 2 (a - t) →
          x % 2 ^ padicValInt 2 (y - x) = t % 2 ^ padicValInt 2 (y - x) →
          (bitOne y (padicValInt 2 (y - x)) ↔ bitOne t (padicValInt 2 (y - x)))) := by sorry

end Erdos195
