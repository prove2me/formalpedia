-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_6_14
-- name    : BeyondGomoryHu.Units.lemma_6_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:52:40.348721+00:00
-- url     : https://prove2.me/theorems/3f12f942-e2d0-4210-bbc9-a361ead52cb3
-- title:
--   Lemma 6.14 — comparability with a shared tied component (corrected: S-cut meets S on both sides)
-- statement:
--   Throughout, $G=(V,E,w)$ is a connected undirected graph with positive integer weights (the standing assumption of Section 2), $\mu$ is a non-leaf node of the skeleton hierarchy $\mathcal T$ and $(H_\mu,\pi_\mu)$ is a connectivity carcass of $\mu$. Let $\alpha$ be a child of $\mu$ (a nonempty node of $H_\mu$) with $x,y\in\alpha$, and $\preceq=\preceq_{(x,y)}$.
--
--   Let $u,v$ be tied to the $\alpha$-component $T$ with $u,v\prec T$ (resp. $u,v\succ T$). Let $\gamma_u$ be an endpoint of $\pi_\mu(u)$ within $T$ and $f_u$ the tree-edge of $\pi_\mu(u)$ adjacent to $\gamma_u$; define $\gamma_v,f_v$ analogously.
--   1. If $f_u\notin\pi_\mu(v)$ then $u\not\preceq v$ (resp. $u\not\succeq v$); symmetrically, if $f_v\notin\pi_\mu(u)$ then $v\not\preceq u$ (resp. $v\not\succeq u$).
--   2. If $f=f_u=f_v$ and $\gamma=\gamma_u=\gamma_v$:
--   $$\sigma_{f,\gamma}(u)<\sigma_{f,\gamma}(v)\Rightarrow u\not\preceq v\ (\text{resp. } u\not\succeq v),$$
--   and symmetrically for $\sigma_{f,\gamma}(v)<\sigma_{f,\gamma}(u)$.
--
--   **Formalization Note.** The carcass is a hypothesis `IsCarcass G μ K` (the properties of Theorems 2.2–2.3); a projection is stored by its two endpoints and its nodes/edges are those of the unique proper path between them. A component is a set of nodes of $H_\mu$, identified with the set of terminals it contains (`compTerms`) when compared with vertex sets. Relations between sets use `SameUnitSets` and `SetPrec` (all pairs). $\sigma_{f,\gamma}$ ranges over every numbering with the properties of Lemma 6.3 (`IsSigma`).
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
--   - generalization: the carcass of µ (the skeleton H_µ of Theorem 2.2 with the projections of Theorem 2.3) → any carcass data K satisfying IsCarcass G µ K, i.e. the properties listed in Theorems 2.2 and 2.3; reason: the paper uses only these properties ("It assumes only the preliminary tools from Section 2 as black boxes", p. 4); its carcass satisfies them, so the statement specializes to the source
--   - encoding: µ a non-leaf node of T, α its child that is a nonempty node of H_µ with x, y ∈ α → µ a node of T with |µ| ≥ 2, carcass K of µ, a node a of H_µ with x, y ∈ terms(a); reason: the children of µ are the nonempty nodes of H_µ (Theorem 2.2); same instances
--   - reading: σ_{f,γ}, "the" numbering of Lemma 6.3 → every numbering satisfying the two properties of Lemma 6.3; reason: Lemma 6.3 asserts existence only; the proof uses only its first property
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 6.14 (Comparability with shared tied component), p. 27 (PDF 29)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_6_14 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (μ : Finset V) (hμ : IsNode G μ) (hμ2 : 2 ≤ μ.card)
    {N : Type} [Fintype N] (K : Carcass V N) (hK : IsCarcass G μ K)
    (a : N) (x y : V) (hx : x ∈ K.terms a) (hy : y ∈ K.terms a) (T : Set N) (hT : IsAlphaComp K a T) (u v : V)
    (hu : Tied K T u) (hv : Tied K T v) (γu γv : N) (fu fv : Sym2 N)
    (hγu : (γu = (K.proj u).1 ∨ γu = (K.proj u).2) ∧ γu ∈ T)
    (hγv : (γv = (K.proj v).1 ∨ γv = (K.proj v).2) ∧ γv ∈ T)
    (hfu : fu ∈ projEdges K u ∧ γu ∈ fu ∧ IsTreeEdge K.H fu)
    (hfv : fv ∈ projEdges K v ∧ γv ∈ fv ∧ IsTreeEdge K.H fv) :
    -- the case `u, v ≺ T`
    (SetStrict G x y {u} (compTerms K T) ∧ SetStrict G x y {v} (compTerms K T) →
      ((fu ∉ projEdges K v → ¬ Prec G x y u v) ∧ (fv ∉ projEdges K u → ¬ Prec G x y v u)) ∧
      (fu = fv → γu = γv → ∀ (c : N) (σ : V → ℕ), fu = s(c, γu) → IsSigma G μ K c γu σ →
        (σ u < σ v → ¬ Prec G x y u v) ∧ (σ v < σ u → ¬ Prec G x y v u))) ∧
    -- the case `u, v ≻ T` ("resp.")
    (SetStrict G x y (compTerms K T) {u} ∧ SetStrict G x y (compTerms K T) {v} →
      ((fu ∉ projEdges K v → ¬ Prec G x y v u) ∧ (fv ∉ projEdges K u → ¬ Prec G x y u v)) ∧
      (fu = fv → γu = γv → ∀ (c : N) (σ : V → ℕ), fu = s(c, γu) → IsSigma G μ K c γu σ →
        (σ u < σ v → ¬ Prec G x y v u) ∧ (σ v < σ u → ¬ Prec G x y u v))) := by sorry

end BeyondGomoryHu.Units
