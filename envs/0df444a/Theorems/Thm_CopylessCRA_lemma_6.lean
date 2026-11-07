-- Prove2me | Theorems.Thm_CopylessCRA_lemma_6
-- name    : CopylessCRA.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:34.932202+00:00
-- url     : https://prove2.me/theorems/136db374-a3e3-4a04-8833-9600220130b0
-- title:
--   Lemma 6, p.7 — a generating submonoid is Zariski dense; $\Gamma\cap\mathcal G^\circ$ is normal of finite index
-- statement:
--   Let $S\subseteq GL_d(\mathbb Q)$ be a submonoid generating the group $\Gamma$, and let $\mathcal G\subseteq GL_d(\overline{\mathbb Q})$ be the Zariski closure of $\Gamma$. Then
--
--   1. $S$ is Zariski dense in $\mathcal G$, and $S\cap\mathcal G^\circ$ is Zariski dense in $\mathcal G^\circ$;
--   2. $\Gamma\cap\mathcal G^\circ$ is Zariski dense in $\mathcal G^\circ$;
--   3. $\Gamma\cap\mathcal G^\circ$ is a normal subgroup of finite index in $\Gamma$.
--
--   The lemma lets the word matrices (a monoid) stand in for the group in all closure arguments.
--
--   Differences from the source:
--   - encoding: $S\cap\mathcal G^\circ$, $\Gamma\cap\mathcal G^\circ$ for $S,\Gamma\subseteq GL_d(\mathbb Q)$ → images of $S$, $\Gamma$ in $GL_d(\overline{\mathbb Q})$ intersected with $\mathcal G^\circ$; the subgroup $\Gamma\cap\mathcal G^\circ$ as the preimage; reason: the inclusion $GL_d(\mathbb Q)\to GL_d(\overline{\mathbb Q})$ is injective
--   - encoding: "the same holds for $\Gamma$" → clause 2 ($\Gamma\cap\mathcal G^\circ$ dense in $\mathcal G^\circ$); $\Gamma$ dense in $\mathcal G$ is the definition of $\mathcal G$; reason: nothing is dropped
--   - encoding: Zariski closure via polynomials in the entries and $\det^{-1}$ → polynomials in the entries, closed sets taken relative to $GL_d(\overline{\mathbb Q})$; reason: multiplying by a power of $\det$, a unit on $GL$, gives the same closed subsets of $GL$
--   - encoding: identity component $\mathcal G^\circ$ of the algebraic group → the union of all Zariski-connected subsets of $\mathcal G$ containing $1$ (the connected component of $1$); reason: this is the identity component of a linear algebraic group; its group and finite-index properties (A1) are theorems, not definitions
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Lemma 6, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_CopylessCRA_zariskiClosure

namespace CopylessCRA

/-- **Lemma 6.** Let `S ⊆ GL_d(ℚ)` be a submonoid generating the group `Γ`, with Zariski closure `𝒢` of
`Γ`. Then `S` is Zariski dense in `𝒢`, and `S ∩ 𝒢°` is Zariski dense in `𝒢°`. The same holds for `Γ`,
and `Γ ∩ 𝒢°` is a normal subgroup of finite index in `Γ`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Lemma 6, p.7 (PDF p.9).

**Formalization Note** Closures are taken in `GL_d(ℚ̄)` (§2.3); "dense in `X`" is "Zariski closure
equals `X`". `Γ ∩ 𝒢°` is the set of `g ∈ Γ` whose image in `GL_d(ℚ̄)` lies in `𝒢°`. -/
theorem lemma_6 {d : ℕ} (S : Submonoid (Matrix (Fin d) (Fin d) ℚ)ˣ) :
    zariskiClosure (toGLK (K := Qbar) '' (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ)) =
        zariskiClosure (toGLK '' (Subgroup.closure (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) :
          Set (Matrix (Fin d) (Fin d) ℚ)ˣ)) ∧
    zariskiClosure (toGLK (K := Qbar) '' (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) ∩
        identityComponent (zariskiClosure (toGLK '' (Subgroup.closure
          (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) : Set (Matrix (Fin d) (Fin d) ℚ)ˣ)))) =
      identityComponent (zariskiClosure (toGLK '' (Subgroup.closure
          (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) : Set (Matrix (Fin d) (Fin d) ℚ)ˣ))) ∧
    zariskiClosure (toGLK (K := Qbar) '' (Subgroup.closure (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) :
          Set (Matrix (Fin d) (Fin d) ℚ)ˣ) ∩
        identityComponent (zariskiClosure (toGLK '' (Subgroup.closure
          (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) : Set (Matrix (Fin d) (Fin d) ℚ)ˣ)))) =
      identityComponent (zariskiClosure (toGLK '' (Subgroup.closure
          (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) : Set (Matrix (Fin d) (Fin d) ℚ)ˣ))) ∧
    ∃ Γ₀ : Subgroup (Matrix (Fin d) (Fin d) ℚ)ˣ,
      (Γ₀ : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) =
        {g | g ∈ Subgroup.closure (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) ∧
          toGLK (K := Qbar) g ∈ identityComponent (zariskiClosure (toGLK '' (Subgroup.closure
            (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ) : Set (Matrix (Fin d) (Fin d) ℚ)ˣ)))} ∧
      (Γ₀.subgroupOf (Subgroup.closure (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ))).Normal ∧
      (Γ₀.subgroupOf (Subgroup.closure (S : Set (Matrix (Fin d) (Fin d) ℚ)ˣ))).FiniteIndex := by sorry

end CopylessCRA
