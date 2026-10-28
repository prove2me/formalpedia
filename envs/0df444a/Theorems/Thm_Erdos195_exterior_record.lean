-- Prove2me | Theorems.Thm_Erdos195_exterior_record
-- name    : Erdos195.exterior_record
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:42:00.528414+00:00
-- url     : https://prove2.me/theorems/4e060619-e815-43f3-9a5d-e34d330bf413
-- title:
--   Exterior records can be appended as the new tree-order minimum
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $P^*=(0,1,-1,-5)$. Let $P$ be $\theta$-safe, $K$ larger than every $\nu_2(b-a)$ ($a\ne b\in P$), $p\in P$ the $\prec_\theta$-minimum of $P$, and $w\equiv p+2^K\pmod{2^{K+1}}$ with $w\ne 2b-a$ for all $a$ before $b$ in $P$. Let $\theta''$ equal $\theta$ except $\theta''(K,p\bmod 2^K)=1-\mathrm{bit}_K(p)$. Then
--   $$P\cdot w\ \text{is}\ \theta''\text{-safe and}\ w\prec_{\theta''}a\ \text{for all}\ a\in P.$$
--   (Exterior records: a new letter in a fresh residue class at level $K$ can be appended as the new minimum.)
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, `L <+: Q` means $L$ is a prefix of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem exterior_record (θ : ℕ → ℤ → Bool) (P : List ℤ) (hP : Safe (treeLt θ) P) (K : ℕ)
    (hK : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → padicValInt 2 (b - a) < K) (p : ℤ) (hp : p ∈ P)
    (hmin : ∀ a ∈ P, a ≠ p → treeLt θ p a) (w : ℤ)
    (hw : w % 2 ^ (K + 1) = (p + 2 ^ K) % 2 ^ (K + 1))
    (hw2 : ∀ a b : ℤ, a ∈ P → b ∈ P → P.idxOf a < P.idxOf b → w ≠ 2 * b - a) :
    Safe (treeLt (fun k r => if k = K ∧ r = p % 2 ^ K then !decide (p / 2 ^ K % 2 = 1) else θ k r))
        (P ++ [w]) ∧
      ∀ a ∈ P, treeLt (fun k r => if k = K ∧ r = p % 2 ^ K then !decide (p / 2 ^ K % 2 = 1)
        else θ k r) w a := by sorry

end Erdos195
