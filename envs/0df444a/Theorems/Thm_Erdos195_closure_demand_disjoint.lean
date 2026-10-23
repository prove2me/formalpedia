-- Prove2me | Theorems.Thm_Erdos195_closure_demand_disjoint
-- name    : Erdos195.closure_demand_disjoint
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:33:29.380153+00:00
-- url     : https://prove2.me/theorems/15a92dcf-836b-4680-921f-0e887b5ca1e0
-- title:
--   Closure-demand bound: disjoint conflicting demands force $n$ new letters
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $Q$ be $\theta$-safe for some tree witness and $V$ a finite set. Suppose for $i=1,\dots,n$ the in-order pairs $(a_i,b_i)$, $(a'_i,b'_i)$ of $Q$ lie at the same node ($\nu_2(b_i-a_i)=\nu_2(b'_i-a'_i)=k_i$, $a_i\equiv a'_i$ mod $2^{k_i}$) but $\mathrm{bit}_{k_i}(b_i)\neq\mathrm{bit}_{k_i}(b'_i)$, and the demand sets
--   $$D_i=\{2b_i-a_i,\,3b_i-2a_i,\,2b'_i-a'_i,\,3b'_i-2a'_i\}$$
--   are pairwise disjoint and disjoint from $V$. Then $|Q\setminus V|\ge n$. (Each conflict must be closed by a letter of $D_i$.)
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem closure_demand_disjoint (Q : List ℤ) (hQ : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q)
    (V : Finset ℤ) (n : ℕ) (a b a' b' : Fin n → ℤ) (D : Fin n → Finset ℤ)
    (hD : ∀ i, D i = {2 * b i - a i, 3 * b i - 2 * a i, 2 * b' i - a' i, 3 * b' i - 2 * a' i})
    (hmem : ∀ i, a i ∈ Q ∧ b i ∈ Q ∧ a' i ∈ Q ∧ b' i ∈ Q)
    (hord : ∀ i, Q.idxOf (a i) < Q.idxOf (b i) ∧ Q.idxOf (a' i) < Q.idxOf (b' i))
    (hlev : ∀ i, padicValInt 2 (b i - a i) = padicValInt 2 (b' i - a' i))
    (hres : ∀ i, a i % 2 ^ padicValInt 2 (b i - a i) = a' i % 2 ^ padicValInt 2 (b i - a i))
    (hconf : ∀ i, ¬ (bitOne (b i) (padicValInt 2 (b i - a i)) ↔
      bitOne (b' i) (padicValInt 2 (b i - a i))))
    (hdisj : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (hV : ∀ i, Disjoint (D i) V) :
    n ≤ (Q.toFinset \ V).card := by sorry

end Erdos195
