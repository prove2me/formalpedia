-- Prove2me | Theorems.Thm_CopylessCRA_lemma_5
-- name    : CopylessCRA.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:50.587813+00:00
-- url     : https://prove2.me/theorems/16edbac1-b25b-4a28-bfb8-fcdb33ebdf65
-- title:
--   Lemma 5 (Rational splitting and weights), p.7 — $H=T\ltimes U$ over $\mathbb Q$ with rational weight spaces
-- statement:
--   Let $H\le GL_d(\overline{\mathbb Q})$ be a Zariski-closed subgroup that is connected, defined over $\mathbb Q$, and triangularizable over $\mathbb Q$. Then:
--
--   1. the unipotent elements of $H$ form a subgroup $U$: closed, connected, normal in $H$, defined over $\mathbb Q$, and containing every closed connected normal unipotent subgroup of $H$ (its connected unipotent radical);
--   2. there is a split torus $T\le H$ defined over $\mathbb Q$ such that multiplication $T\times U\to H$ is an isomorphism of varieties: every $h\in H$ is $h=\tau(h)\upsilon(h)$ with $\tau(h)\in T$, $\upsilon(h)\in U$, the maps $\tau,\upsilon$ are given by rational polynomials in the entries and $\det^{-1}$, and $\tau(tu)=t$, $\upsilon(tu)=u$;
--   3. $H(\mathbb Q)=T(\mathbb Q)U(\mathbb Q)$;
--   4. every rational representation of $T$ decomposes into rational weight spaces;
--   5. so does the conjugation action of $T$ on $\mathrm{Lie}(U)$.
--
--   This is the structure used to build the normal-form machine in §5.
--
--   Differences from the source:
--   - encoding: $\mathrm{Lie}(U)$ → $\log U=\{X$ nilpotent$:\exp(sX)\in U\ \forall s\}$, with its rational weight decomposition by $\mathbb Q$-subspaces whose $\overline{\mathbb Q}$-span is $\mathrm{Lie}(U)$; reason: in characteristic zero the Lie algebra of a unipotent group is $\log U$ (§2.3, §5)
--   - reading: "multiplication $T\times U\to H$ is an isomorphism of varieties" → the inverse $h\mapsto(\tau(h),\upsilon(h))$ is given by polynomials with rational coefficients in the entries and $\det^{-1}$; reason: the proof states the isomorphism over $\mathbb Q$; this is the stronger reading
--   - encoding: split torus defined over $\mathbb Q$; connected unipotent radical → closed connected subgroup defined over $\mathbb Q$ and diagonalized by a rational basis; the largest closed connected normal unipotent subgroup; reason: standard definitions (Borel §8, §11)
--   - encoding: $H\le GL_d$ connected → $H$ a Zariski-closed subgroup of $GL_d(\overline{\mathbb Q})$, Zariski connected; reason: $H$ is a linear algebraic group
--   - encoding: Zariski closure via polynomials in the entries and $\det^{-1}$ → polynomials in the entries, closed sets taken relative to $GL_d(\overline{\mathbb Q})$; reason: multiplying by a power of $\det$, a unit on $GL$, gives the same closed subsets of $GL$
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Lemma 5, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_CopylessCRA_zariskiClosure
import Definitions.Def_CopylessCRA_IsSplitTorusQ

namespace CopylessCRA

/-- **Lemma 5 (Rational splitting and weights).** Let `H ≤ GL_d` be connected, defined over `ℚ`, and
triangularizable over `ℚ`. Its unipotent elements form its connected unipotent radical `U`, defined
over `ℚ`. There is a split torus `T` defined over `ℚ` such that multiplication `T × U → H` is an
isomorphism of varieties. In particular `H(ℚ) = T(ℚ)U(ℚ)`. Every rational representation of `T`,
including its conjugation action on `Lie(U)`, decomposes into rational weight spaces.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Lemma 5, p.7 (PDF p.9).

**Formalization Note** `H` is a Zariski-closed subgroup of `GL_d(ℚ̄)` (an algebraic group), connected
in the Zariski topology. `U` is the set of unipotent elements of `H`; the conclusion says it is a
closed, connected, normal subgroup of `H`, defined over `ℚ`, containing every closed connected normal
unipotent subgroup (the unipotent radical). "Isomorphism of varieties" is: multiplication is a
bijection `T × U → H` whose inverse `h ↦ (τ h, υ h)` is given by polynomials with rational
coefficients in the entries and `det⁻¹` (the proof gives the isomorphism over `ℚ`). `X(ℚ)` is the set
of points of `X` with rational entries. A split torus over `ℚ` is a closed connected subgroup defined
over `ℚ` and diagonalized by a rational change of basis (`IsSplitTorusQ`). A rational representation
is a homomorphism `T → GL_n(ℚ̄)` given by rational polynomials in the entries and `det⁻¹`.
`Lie(U) = log U` (`lieAlg`), and its decomposition is by `ℚ`-subspaces of rational matrices whose
`ℚ̄`-span is `Lie(U)`. -/
theorem lemma_5 {d : ℕ} (H : Subgroup (Matrix (Fin d) (Fin d) Qbar)ˣ)
    (hcl : IsZariskiClosed (H : Set (Matrix (Fin d) (Fin d) Qbar)ˣ)) (hconn : IsZariskiConnected (H : Set (Matrix (Fin d) (Fin d) Qbar)ˣ))
    (hdef : IsDefinedOverQ (H : Set (Matrix (Fin d) (Fin d) Qbar)ˣ)) (htri : IsTriangularizableQ (H : Set (Matrix (Fin d) (Fin d) Qbar)ˣ)) :
    ∃ U : Subgroup (Matrix (Fin d) (Fin d) Qbar)ˣ,
      (U : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) = {g | g ∈ H ∧ IsUnipotent (g : Matrix (Fin d) (Fin d) Qbar)} ∧
      (U.subgroupOf H).Normal ∧ IsZariskiClosed (U : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) ∧
      IsZariskiConnected (U : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) ∧ IsDefinedOverQ (U : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) ∧
      (∀ V : Subgroup (Matrix (Fin d) (Fin d) Qbar)ˣ, V ≤ H → IsZariskiClosed (V : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) →
        IsZariskiConnected (V : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) → (V.subgroupOf H).Normal →
        (∀ g ∈ V, IsUnipotent (g : Matrix (Fin d) (Fin d) Qbar)) → V ≤ U) ∧
      ∃ T : Subgroup (Matrix (Fin d) (Fin d) Qbar)ˣ, T ≤ H ∧ IsSplitTorusQ T ∧
        (∃ τ υ : (Matrix (Fin d) (Fin d) Qbar)ˣ → (Matrix (Fin d) (Fin d) Qbar)ˣ,
          IsRegularQ (fun g => (τ g : Matrix (Fin d) (Fin d) Qbar)) (H : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) ∧
          IsRegularQ (fun g => (υ g : Matrix (Fin d) (Fin d) Qbar)) (H : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) ∧
          (∀ h ∈ H, τ h ∈ T ∧ υ h ∈ U ∧ τ h * υ h = h) ∧
          ∀ t ∈ T, ∀ u ∈ U, τ (t * u) = t ∧ υ (t * u) = u) ∧
        {h : (Matrix (Fin d) (Fin d) Qbar)ˣ | h ∈ H ∧ IsRationalPt (h : Matrix (Fin d) (Fin d) Qbar)} =
          {h | ∃ t ∈ T, ∃ u ∈ U, IsRationalPt (t : Matrix (Fin d) (Fin d) Qbar) ∧
            IsRationalPt (u : Matrix (Fin d) (Fin d) Qbar) ∧ h = t * u} ∧
        (∀ (n : ℕ) (ρ : T →* (Matrix (Fin n) (Fin n) Qbar)ˣ),
          IsRationalRep T ρ → HasRationalWeightDecomp T ρ) ∧
        HasRationalLieWeightDecomp T (U : Set (Matrix (Fin d) (Fin d) Qbar)ˣ) := by sorry

end CopylessCRA
