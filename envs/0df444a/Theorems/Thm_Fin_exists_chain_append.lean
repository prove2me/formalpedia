-- Prove2me | Theorems.Thm_Fin_exists_chain_append
-- name    : Fin.exists_chain_append
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/79579f25-6188-5a2d-847b-790540041a41
-- title:
--   Concatenation of finite S-chains
-- statement:
--   Let $\alpha$ be a type, let $S$ be an arbitrary binary relation on $\alpha$, and let $a,b,c\in\alpha$. Call $x$ joined to $y$ by an $S$-chain if there exist $n\in\mathbb{N}$ and a map $f\colon \mathrm{Fin}(n+1)\to\alpha$ with $f(0)=x$, $f(\mathrm{last}\,n)=y$ and $S(f(\mathrm{castSucc}\,i),f(\mathrm{succ}\,i))$ for every $i\in\mathrm{Fin}(n)$, i.e. a finite sequence $x=f_0,f_1,\dots,f_n=y$ each of whose consecutive pairs is related by $S$ (the case $n=0$ being allowed, which forces $x=y$). The theorem asserts: if $a$ is joined to $b$ by an $S$-chain and $b$ is joined to $c$ by an $S$-chain, then $a$ is joined to $c$ by an $S$-chain. In other words, the relation "joined by a finite $S$-chain" is transitive. Note that the length of the resulting chain is not recorded in the conclusion: only the existence of some $n$ and some $f$ is asserted, not that $n$ is the sum of the two given lengths.
--
--   This is the elementary transitivity of the relation "there is a finite chain from $x$ to $y$ with consecutive terms related by $S$", stated in exactly the shape (`Fin (n + 1)`-indexed sequence with endpoints $0$ and `Fin.last n` and a condition on each consecutive pair) in which filtrations of modules are recorded in this development. It is used to splice two such filtrations sharing an endpoint into a single one, in the construction of chains of subgroups with prescribed step conditions and in the verification of the admissibility condition for the Eisenstein-primary torsion of a modular Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Fin_exists_chain_append.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Fin.exists_chain_append {α : Type*} (S : α → α → Prop) {a b c : α}
    (h₁ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = b ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ))
    (h₂ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = b ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ)) :
    ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ) := by sorry
