-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_eta_eq_of_isLocalRing
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isAdmissible_eta_eq_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/74ddf529-095b-588c-855d-1f7abab48f69
-- title:
--   Admissible rigidified object over a local Noetherian base
-- statement:
--   Fix a prime $p$, a commutative ring $O$, a ring homomorphism $\iota\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to O$, and a formal $\mathcal{O}_D$-module $\Phi$ over $O/pO$ (a $2$-dimensional commutative formal group law together with an action of $\mathbb{Z}_{p^2}$ and a series $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[a^{\sigma}]\circ\varpi$). Let $M$ be a moduli package over $O$: an assignment $B\mapsto M(B,\psi)$ for commutative rings $B$ with a map $\psi\colon O\to B$ and $p$ nilpotent in $B$, functorial in $O$-algebra maps. Let $\eta$ assign, to every such $(B,\psi)$ and every rigidified object $t$ over $B$ (a formal $\mathcal{O}_D$-module $t.X$ over $B$, an integer $t.n$, and a series $t.\rho$ over $B/pB$), a point $\eta(t)\in M(B,\psi)$. Assume the Zariski-local admissible surjectivity hypothesis $h\eta$: for every Noetherian $(B,\psi)$ with $p$ nilpotent and every $m\in M(B,\psi)$ there is a finite family $f_1,\dots,f_n\in B$ generating the unit ideal such that for each $i$ and each Noetherian localisation $L$ of $B$ away from $f_i$ in which $p$ is nilpotent, some rigidified object $t$ over $L$ is admissible for $\iota$ and $\psi$ composed with $B\to L$ — i.e. $t.X$ is special for the induced structure map, has height $4$, and $t.\rho$ is an isogeny of height $4\,t.n$ from the reduction of $\Phi$ to the reduction of $t.X$ — and satisfies $\eta(t)=$ the image of $m$ in $M(L,\cdot)$. The conclusion: for every Noetherian local $B$ with $\psi\colon O\to B$ and $p$ nilpotent in $B$, and every $m\in M(B,\psi)$, there is a rigidified object $t$ over $B$ which is admissible for $\iota$ and $\psi$ and satisfies $\eta(t)=m$.
--
--   This removes the Zariski localisation from the third clause of the period-map framework in the Čerednik–Drinfeld uniformisation: over a local base the local surjectivity of $\eta$ onto admissible rigidified objects becomes surjectivity on the nose. It is used where the base is a residue field or a ring of dual numbers, in the identification of period maps and in the edge-chart bijectivity statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_isAdmissible_eta_eq_of_isLocalRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_isAdmissible_eta_eq_of_isLocalRing
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (M : ModuliPackage.{0, 0} p O)
    (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
      ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
          (hL : IsNilpotent (p : L)),
          ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
            η L ((algebraMap B L).comp ψ) hL t = M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)
    (B : Type) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) :
    ∃ t : Rigidified p Φ B, t.IsAdmissible ι ψ ∧ η B ψ hB t = m := by sorry
