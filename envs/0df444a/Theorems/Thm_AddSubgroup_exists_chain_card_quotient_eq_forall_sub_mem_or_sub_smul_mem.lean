-- Prove2me | Theorems.Thm_AddSubgroup_exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
-- name    : AddSubgroup.exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/61775372-9b7d-5c58-a50e-607838e51143
-- title:
--   Admissible filtration with steps of prime order q
-- statement:
--   Let $\Gamma$ be a group, $M$ an additive abelian group, and $\varphi \colon \Gamma \to \mathrm{Aut}(M)$ a homomorphism into the additive automorphism group of $M$; let $q$ be a prime and $\chi \colon \Gamma \to (\mathbb{Z}/q)^\times$ a homomorphism, and for $g \in \Gamma$ write $c_g = (\chi(g))\!.\mathrm{val} \in \{0,\dots,q-1\}$ for the canonical natural-number representative of $\chi(g)$, acting on $M$ by iterated addition. Let $A \le B$ be additive subgroups of $M$ with $B/A$ finite, both stable under $\varphi$ in the sense that $\varphi(g)x \in A$ for all $g \in \Gamma$, $x \in A$, and likewise for $B$, such that $q x \in A$ for every $x \in B$, and such that $(\varphi(g) - 1)\bigl(\varphi(g)x - c_g x\bigr) \in A$ for all $g \in \Gamma$ and $x \in B$. Then there exist $n \in \mathbb{N}$ and a family $M_0,\dots,M_n$ of additive subgroups of $M$, indexed by $\mathrm{Fin}(n+1)$, with $M_0 = A$ and $M_n = B$, such that for each $i < n$ one has $M_i \le M_{i+1}$, the quotient $M_{i+1}/M_i$ has cardinality exactly $q$, and either $\varphi(g)x - x \in M_i$ for all $g \in \Gamma$ and $x \in M_{i+1}$, or $\varphi(g)x - c_g x \in M_i$ for all $g \in \Gamma$ and $x \in M_{i+1}$.
--
--   This is the existence of an admissible filtration in Mazur's sense: the condition $(g-1)(g-\chi(g)) = 0$ on the finite $\mathbb{F}_q[\Gamma]$-module $B/A$ forces a chain from $A$ to $B$ with steps of order $q$ on each of which $\Gamma$ acts trivially or through $\chi$. It is used to verify admissibility of the Eisenstein-primary torsion of the Jacobian, via [`ModularCurve.eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar`](thm.html#ModularCurve.eisensteinPrimaryTorsion_isMazurAdmissible_heckeModuleBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem.lean

import Mathlib
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AddSubgroup.exists_chain_card_quotient_eq_forall_sub_mem_or_sub_smul_mem
    {Γ M : Type*} [Group Γ] [AddCommGroup M] (φ : Γ →* AddAut M) {q : ℕ} (hq : q.Prime)
    (χ : Γ →* (ZMod q)ˣ) (A B : AddSubgroup M) (hAB : A ≤ B)
    (hfin : Finite (↥B ⧸ A.addSubgroupOf B))
    (hA : ∀ g : Γ, ∀ x ∈ A, φ g x ∈ A) (hB : ∀ g : Γ, ∀ x ∈ B, φ g x ∈ B)
    (hqB : ∀ x ∈ B, q • x ∈ A)
    (h : ∀ g : Γ, ∀ x ∈ B,
      φ g (φ g x - (χ g : ZMod q).val • x) - (φ g x - (χ g : ZMod q).val • x) ∈ A) :
    ∃ (n : ℕ) (step : Fin (n + 1) → AddSubgroup M), step 0 = A ∧ step (Fin.last n) = B ∧
      ∀ i : Fin n, step i.castSucc ≤ step i.succ ∧
        Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = q ∧
        ((∀ g : Γ, ∀ x ∈ step i.succ, φ g x - x ∈ step i.castSucc) ∨
         (∀ g : Γ, ∀ x ∈ step i.succ, φ g x - (χ g : ZMod q).val • x ∈ step i.castSucc)) := by sorry
