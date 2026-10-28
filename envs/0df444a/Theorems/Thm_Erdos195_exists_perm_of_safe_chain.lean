-- Prove2me | Theorems.Thm_Erdos195_exists_perm_of_safe_chain
-- name    : Erdos195.exists_perm_of_safe_chain
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:13:40.545494+00:00
-- url     : https://prove2.me/theorems/870d2a30-0418-4a5d-aa95-b17b37a84f5d
-- title:
--   Limit lemma: nested safe words (any stage orders, e.g. tree orders) covering $\mathbb{Z}$ give a 4-AP-free bijection
-- statement:
--   Let $R_n$ ($n\in\mathbb{N}$) be arbitrary relations on $\mathbb{Z}$. For a finite word $P$, the completion orders $\mathbb{Z}$ by listing $P$ first and then all other integers in $R$-order; $P$ is $R$-safe if this completion contains no $a$, $r\neq0$ with $a,a+r,a+2r,a+3r$ appearing in this order. Suppose $P_0,P_1,\dots$ are duplicate-free finite words, each $P_n$ is $R_n$-safe, each $P_n$ is a prefix of $P_{n+1}$, and every integer occurs in some $P_n$. Then
--   $$\exists f:\mathbb{N}\to\mathbb{Z}\ \text{bijective with no monotone 4-term arithmetic progression}.$$
--   This is the limit lemma (L): in particular nested tree-safe words ($R_n=\prec_{\theta_n}$, witnesses may change with $n$) covering $\mathbb{Z}$ would answer Erdős Problem 195 with $3$.
--
--   Formalization note: prefix is `<+:`; the conclusion is `∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4` with `HasMonotoneAP` from `Definitions.Def_Erdos195_defs` (verbatim formal-conjectures definition).
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem exists_perm_of_safe_chain (R : ℕ → ℤ → ℤ → Prop) (P : ℕ → List ℤ)
    (hsafe : ∀ n, Safe (R n) (P n)) (hnd : ∀ n, (P n).Nodup)
    (hpre : ∀ n, P n <+: P (n + 1)) (hcov : ∀ x : ℤ, ∃ n, x ∈ P n) :
    ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 4 := by sorry

end Erdos195
