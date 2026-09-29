-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_and_apply_eq_of_isLocalRing
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isAdmissible_and_apply_eq_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/0f5f96fc-4ff2-5a6d-bd77-fb2269204982
-- title:
--   Admissible rigidification over a Noetherian local base
-- statement:
--   Fix a prime $p$ and a commutative ring $O$ with a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to O$ from the Witt vectors of the field with $p^2$ elements, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$, i.e. a two-dimensional commutative formal group law together with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of the law, additive and multiplicative in the acting parameter, and an endomorphism $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma(a)] \circ \varpi$ for Witt-vector Frobenius $\sigma$. Let $M$ be a moduli package over $O$: an assignment $(B,\psi : O \to B, p$ nilpotent in $B) \mapsto M.\mathrm{obj}$, with functorial transport along ring homomorphisms compatible with the structure maps, satisfying the identity and composition laws. Let $\eta$ be a family of maps, for every such $(B,\psi)$, from rigidified data over $B$ — a formal $\mathcal{O}_D$-module $X$ over $B$, an integer $n$, and a pair $\rho$ of power series in two variables over $B/pB$ — to $M.\mathrm{obj}$. Assume the covering hypothesis $h\eta_3$: for every Noetherian $B$, every $\psi$, every witness that $p$ is nilpotent in $B$, and every $m \in M.\mathrm{obj}$, there are finitely many elements $f_0,\dots,f_{n-1}$ of $B$ generating the unit ideal such that for each $i$ and each Noetherian $B$-algebra $L$ realising the localisation of $B$ away from $f_i$ in which $p$ is nilpotent, some rigidified $t$ over $L$ is admissible for $(\iota, (\mathrm{algebraMap}) \circ \psi)$ — that is, its formal $\mathcal{O}_D$-module is special for the induced structure map, has height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$ — and satisfies $\eta(t) = M.\mathrm{map}(m)$. Then for $B$ Noetherian and local, with $\psi : O \to B$, $p$ nilpotent in $B$, and $m \in M.\mathrm{obj}$, there exists a rigidified $t$ over $B$ that is admissible for $(\iota,\psi)$ with $\eta(t) = m$.
--
--   This is the statement that over a local base no localisation is needed: every point of a moduli package is already represented by an admissible rigidified formal $\mathcal{O}_D$-module over the base itself, upgrading the Zariski-local representability hypothesis to an absolute one. It is used in the Čerednik–Drinfeld part of the development, in particular for the surjectivity of the dictionary between rigidified data and the supersingular moduli over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_and_apply_eq_of_isLocalRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isAdmissible_and_apply_eq_of_isLocalRing
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (M : ModuliPackage.{0, 0} p O)
    (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → M.obj B ψ hB)

    (hη₃ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)

    (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) :
    ∃ t : Rigidified p Φ B, t.IsAdmissible ι ψ ∧ η B ψ hB t = m := by sorry
