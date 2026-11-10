-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_6_4
-- name    : AlmostLinSubsetSum.Main.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:48.062736+00:00
-- url     : https://prove2.me/theorems/e10a6329-8f36-4c57-8dc3-1943b70ce914
-- title:
--   Lemma 6.4 — the extended zonotope $\hat Z=(F,\psi)(J)$: generators, full dimension, convex/concave chords, short chord over the pivot
-- statement:
--   **Lemma 6.4** (The extended zonotope, p. 29). With $\hat v_i:=(v_i,\psi\cdot u_i)=(Fu_i,\psi\cdot u_i)\in\mathbb Z^{d+1}$ and $\hat Z:=\{(Fu,\psi\cdot u):u\in J\}$:
--
--   (i) $\hat Z=\sum_{i\in I_G}[0,\hat v_i]$, and the projection of $\hat Z$ to the first $d$ coordinates is $FJ$;
--   (ii) $\hat Z$ is full-dimensional: the map $u\mapsto(Fu,\psi\cdot u)$ has rank $d+1$;
--   (iii) for $y\in FJ$ the vertical chord of $\hat Z$ over $y$ is $\{y\}\times[\psi^-(y),\psi^+(y)]$; $\psi^-$ is convex and $\psi^+$ is concave on $FJ$, and they describe the lower and upper boundary of $\hat Z$: $\hat Z=\{(y,z): y\in FJ,\ \psi^-(y)\le z\le\psi^+(y)\}$;
--   (iv) the chord over the pivot is short: $0\le\psi^+(t_0)-\psi^-(t_0)\le c_{\mathrm{flat}}(r)$.
--
--   Setting as hypotheses: $u_i\in\mathbb Z^r$ ($i\in I_G=\{0,\dots,m-1\}$) spanning $\mathbb R^r$; an integer $d\times r$ matrix $F$ of rank $d$ (onto $\mathbb R^d$); $\psi\in\mathbb Z^r$ not orthogonal to $\ker F$; $J=\sum_i[0,u_i]$; $t_0\in\mathbb Z^d$ with $t_0\in FJ$ and $\mathrm{width}_{J\cap F^{-1}(t_0)}(\psi)\le c$ for a real $c\ge1$ standing for $c_{\mathrm{flat}}(r)$.
--
--   Differences from the source:
--   - generalization: the core J, F and ψ of §4–§6 (Theorem 4.2, Lemma 6.3; FJ has nonempty interior by (27), t₀ interior in FJ) → any spanning u_i ∈ ℤ^r, any integer F onto ℝ^d, any ψ not orthogonal to ker F, any t₀ ∈ FJ whose fiber has width ≤ c along ψ; reason: the proof uses only these facts, all implied by the paper's context
--   - generalization: c_flat(r), the flatness constant of Theorem 2.A(iii) (≥ 1) → any real c ≥ 1; reason: the statement for every c ≥ 1 includes c = c_flat(r)
--   - encoding: 'full-dimensional', 'rank d + 1', 'describe the lower and the upper boundary' → interior of Ẑ nonempty; u ↦ (Fu, ψ·u) surjective onto ℝ^{d+1}; Ẑ = {x : proj x ∈ FJ, ψ⁻(proj x) ≤ x_last ≤ ψ⁺(proj x)}; convexity as ConvexOn/ConcaveOn on FJ; reason: a linear map to ℝ^{d+1} has rank d+1 iff it is onto; the boundary description made precise
--   - encoding: ψ^−(y), ψ^+(y) the minimum and maximum of ψ·u over J ∩ F⁻¹(y) → sInf/sSup of the image of the fiber, used only for y ∈ FJ; reason: the fiber is nonempty and compact there, so these are the minimum and maximum
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 6.4, p. 29 (setting pp. 27–29)

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic
import Definitions.Def_AlmostLinSubsetSum_Main_Geometry

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 6.4** (The extended zonotope; Chen, Mao, Zhang 2026, p. 29). With
`v̂_i := (v_i, ψ · u_i) = (F u_i, ψ · u_i) ∈ ℤ^{d+1}` and `Ẑ := {(Fu, ψ · u) : u ∈ J}`:
(i) `Ẑ = Σ_{i∈I_G} [0, v̂_i]`, and the projection of `Ẑ` to the first `d` coordinates is `FJ`;
(ii) `Ẑ` is full-dimensional: the map `u ↦ (Fu, ψ · u)` has rank `d + 1`;
(iii) for `y ∈ FJ` the vertical chord of `Ẑ` over `y` is `{y} × [ψ⁻(y), ψ⁺(y)]`; `ψ⁻` is
convex and `ψ⁺` is concave on `FJ`, and they describe the lower and the upper boundary of `Ẑ`;
(iv) the chord over the pivot is short: `0 ≤ ψ⁺(t₀) − ψ⁻(t₀) ≤ c_flat(r)`.

Setting of §6 as hypotheses: `u_i ∈ ℤ^r` (`i ∈ I_G = {0..m−1}`) spanning `ℝ^r`
(Theorem 4.2(iv)); an integer `d × r` matrix `F` of rank `d` (onto `ℝ^d`); `ψ ∈ ℤ^r` not
orthogonal to `ker F`; `J = Σ_i [0, u_i]`; a pivot `t₀ ∈ FJ` whose fiber `J ∩ F⁻¹(t₀)` has
width at most `c` in direction `ψ` (Lemma 6.3), for a real `c ≥ 1` in place of `c_flat(r)`. -/
theorem lemma_6_4 {d r m : ℕ} (u : Fin m → Fin r → ℤ)
    (hspan : Submodule.span ℝ (Set.range (fun i => toReal (u i))) = ⊤)
    (F : Matrix (Fin d) (Fin r) ℤ) (hF : Function.Surjective (realMap F))
    (ψ : Fin r → ℤ) (hψ : ∃ k : Fin r → ℝ, realMap F k = 0 ∧ toReal ψ ⬝ᵥ k ≠ 0)
    (t₀ : Fin d → ℤ)
    (ht₀ : toReal t₀ ∈ realMap F '' zonotope Finset.univ (fun i => toReal (u i)))
    (c : ℝ) (hc : 1 ≤ c)
    (hflat : widthFn (fiber (zonotope Finset.univ (fun i => toReal (u i))) F (toReal t₀))
      (toReal ψ) ≤ c) :
    -- (i)
    (extMap F ψ '' zonotope Finset.univ (fun i => toReal (u i)) =
        zonotope Finset.univ
          (fun i => toReal (extendInt (F.mulVec (u i)) (ψ ⬝ᵥ u i))) ∧
      proj '' (extMap F ψ '' zonotope Finset.univ (fun i => toReal (u i))) =
        realMap F '' zonotope Finset.univ (fun i => toReal (u i))) ∧
    -- (ii)
    ((interior (extMap F ψ '' zonotope Finset.univ (fun i => toReal (u i)))).Nonempty ∧
      Function.Surjective (extMap F ψ)) ∧
    -- (iii)
    ((∀ y ∈ realMap F '' zonotope Finset.univ (fun i => toReal (u i)),
        {z : ℝ | extend y z ∈ extMap F ψ '' zonotope Finset.univ (fun i => toReal (u i))} =
          Set.Icc (psiMinus (zonotope Finset.univ (fun i => toReal (u i))) F ψ y)
            (psiPlus (zonotope Finset.univ (fun i => toReal (u i))) F ψ y)) ∧
      ConvexOn ℝ (realMap F '' zonotope Finset.univ (fun i => toReal (u i)))
        (psiMinus (zonotope Finset.univ (fun i => toReal (u i))) F ψ) ∧
      ConcaveOn ℝ (realMap F '' zonotope Finset.univ (fun i => toReal (u i)))
        (psiPlus (zonotope Finset.univ (fun i => toReal (u i))) F ψ) ∧
      extMap F ψ '' zonotope Finset.univ (fun i => toReal (u i)) =
        {x : Fin (d + 1) → ℝ |
          proj x ∈ realMap F '' zonotope Finset.univ (fun i => toReal (u i)) ∧
          psiMinus (zonotope Finset.univ (fun i => toReal (u i))) F ψ (proj x) ≤
            x (Fin.last d) ∧
          x (Fin.last d) ≤
            psiPlus (zonotope Finset.univ (fun i => toReal (u i))) F ψ (proj x)}) ∧
    -- (iv)
    (0 ≤ psiPlus (zonotope Finset.univ (fun i => toReal (u i))) F ψ (toReal t₀) -
          psiMinus (zonotope Finset.univ (fun i => toReal (u i))) F ψ (toReal t₀) ∧
      psiPlus (zonotope Finset.univ (fun i => toReal (u i))) F ψ (toReal t₀) -
          psiMinus (zonotope Finset.univ (fun i => toReal (u i))) F ψ (toReal t₀) ≤ c) := by sorry

end AlmostLinSubsetSum.Main
