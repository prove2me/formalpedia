-- Prove2me | Theorems.Thm_Erdos195_fourth_term_node
-- name    : Erdos195.fourth_term_node
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:33:27.885995+00:00
-- url     : https://prove2.me/theorems/5a52b7f4-cc74-4750-9249-13134ad79e49
-- title:
--   Comparison nodes of the fourth term $3b-2a$
-- statement:
--   Let $a\ne b$ be integers, $c=3b-2a$, $k=\nu_2(b-a)$. Then: (i) $\nu_2(c-a)=k$ and $\mathrm{bit}_k(c)=\mathrm{bit}_k(b)$; (ii) $\nu_2(c-b)=k+1$ and $c\equiv b\pmod{2^{k+1}}$; (iii) for $x\ne b$ with $p=\nu_2(b-x)$ and $2^p\mid a-x$ (i.e. $p\le\nu_2(a-x)$ or $x=a$):
--   $$\nu_2(c-x)=p,\qquad \mathrm{bit}_p(c)=\mathrm{bit}_p(b);$$
--   (iv) for $x\ne a$ with $\nu_2(a-x)+1<\nu_2(b-x)$: $\nu_2(c-x)=\nu_2(a-x)+1$. Thus the comparison node of the fourth term $c$ with $x$ coincides with that of $b$ whenever $p\le q$. Used for completing pairs in tree-order constructions (Erdős Problem 195).
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem fourth_term_node (a b : ℤ) (hab : a ≠ b) :
    (padicValInt 2 ((3 * b - 2 * a) - a) = padicValInt 2 (b - a) ∧
      (bitOne (3 * b - 2 * a) (padicValInt 2 (b - a)) ↔ bitOne b (padicValInt 2 (b - a)))) ∧
    (padicValInt 2 ((3 * b - 2 * a) - b) = padicValInt 2 (b - a) + 1 ∧
      (3 * b - 2 * a) % 2 ^ (padicValInt 2 (b - a) + 1) = b % 2 ^ (padicValInt 2 (b - a) + 1)) ∧
    (∀ x : ℤ, x ≠ b → (2 : ℤ) ^ padicValInt 2 (b - x) ∣ a - x →
      padicValInt 2 ((3 * b - 2 * a) - x) = padicValInt 2 (b - x) ∧
      (bitOne (3 * b - 2 * a) (padicValInt 2 (b - x)) ↔ bitOne b (padicValInt 2 (b - x)))) ∧
    (∀ x : ℤ, x ≠ a → padicValInt 2 (a - x) + 1 < padicValInt 2 (b - x) →
      padicValInt 2 ((3 * b - 2 * a) - x) = padicValInt 2 (a - x) + 1) := by sorry

end Erdos195
