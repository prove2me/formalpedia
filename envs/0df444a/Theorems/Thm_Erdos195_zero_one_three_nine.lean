-- Prove2me | Theorems.Thm_Erdos195_zero_one_three_nine
-- name    : Erdos195.zero_one_three_nine
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:41:51.534095+00:00
-- url     : https://prove2.me/theorems/bb53852e-1624-4264-addb-1e256affd3ea
-- title:
--   $(0,1,3)$ is tree-safe but $(0,1,3,9)$ is not
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $P^*=(0,1,-1,-5)$. $(0,1,3)$ is $\theta$-safe for the constant witness $\theta\equiv1$, but
--   $$(0,1,3,9)\ \text{is not tree-safe}:$$
--   the open pairs $(1,3)$ and $(3,9)$ sit at node $(1,1)$ with opposite bits. So being numerically extremal does not make a new letter safe.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, `L <+: Q` means $L$ is a prefix of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem zero_one_three_nine :
    Safe (treeLt fun _ _ => true) [0, 1, 3] ∧
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 3, 9] := by sorry

end Erdos195
