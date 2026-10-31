-- Prove2me | Theorems.Thm_ContactTopology_compact_contact_embedding_isotopy_extension
-- name    : ContactTopology.compact_contact_embedding_isotopy_extension
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:45:09.809739+00:00
-- url     : https://prove2.me/theorems/892b3699-b2de-40cd-b81c-4faa7416642e
-- title:
--   Compactly supported extension of a contact embedding isotopy
-- statement:
--   Let $\alpha=a_0\,dx+a_1\,dy+a_2\,dz$ be a smooth contact form on $\mathbb R^3$, so that $a\cdot\operatorname{curl}a$ is nowhere zero. Let $N\subset\mathbb R^3$ be open and let $g_s:\mathbb R^3\to\mathbb R^3$ be a jointly smooth family, defined for every real parameter $s$, such that $g_0|_N=\mathrm{id}$ and every $g_s|_N$ is injective with injective derivative. Suppose there is a jointly smooth function $\lambda_s$, positive on $N$, for which
--   $$
--   g_s^*\alpha=\lambda_s\alpha\quad\text{on }N\quad\text{for every }s\in\mathbb R.
--   $$
--   Let $K\subset N$ be compact, and let $U$ be any open set containing the entire track $\{g_s(x):0\le s\le1,\ x\in K\}$.
--
--   There exist jointly smooth maps $\Psi_t,R_t:\mathbb R^3\to\mathbb R^3$, a jointly smooth positive function $\Lambda_t$, and a compact set $C\subset U$ such that
--   $$
--   \Psi_0=\mathrm{id},\qquad R_t\circ\Psi_t=\Psi_t\circ R_t=\mathrm{id},
--   \qquad \Psi_t|_{\mathbb R^3\setminus C}=\mathrm{id},
--   $$
--   and, for every $0\le t\le1$,
--   $$
--   \Psi_t^*\alpha=\Lambda_t\alpha,
--   \qquad \Psi_t(x)=g_t(x)\quad(x\in K).
--   $$
--   The inverse identities and common compact support hold for all real times. The contact and agreement conclusions are asserted on the unit interval.
--
--   This is compactly supported contact isotopy extension in Euclidean dimension three, with an explicit smooth inverse and support control in any prescribed neighborhood of the compact track. The embedding family is supplied as actual maps with pullback and derivative identities; the ambient contact isotopy is constructed. This statement does not assume an ambient extension and does not assert the general contact-manifold version or the Legendrian core classification.
-- source:
--   Euclidean dimension-three compact-track form of contact isotopy extension: Geiges, An Introduction to Contact Topology, Theorem 2.6.12, as invoked in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma 2.7(1), proof, printed pp.10–11. The all-real smooth parameter data, global coefficient representative, explicit smooth inverse and prescribed compact-support formulation are stated here as a coordinate specialization. The proof constructs the Hamiltonian and ambient flow; it does not assume the general-manifold extension theorem.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.compact_contact_embedding_isotopy_extension
    (a : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (ha : ContDiff ℝ ∞ a)
    (g : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => g p.1 p.2))
    (lam : ℝ → (Fin 3 → ℝ) → ℝ)
    (hlam : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2))
    (N : Set (Fin 3 → ℝ)) (hN : IsOpen N)
    (hinj : ∀ s, InjOn (g s) N)
    (hder : ∀ s x, x ∈ N → Function.Injective (fderiv ℝ (g s) x))
    (h0 : ∀ x ∈ N, g 0 x=x)
    (K U : Set (Fin 3 → ℝ)) (hK : IsCompact K) (hKN : K ⊆ N) (hU : IsOpen U)
    (htrack : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ U) :
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun p v => p 0*v 0+p 1*v 1+p 2*v 2
    let c : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y =>
      ![fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1,
        fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2,
        fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0]
    (∀ y, B (a y) (c y) ≠ 0) → (∀ s x, x ∈ N → 0 < lam s x) →
    (∀ s x, x ∈ N → ∀ v, B (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*B (a x) v) →
    ∃ ψ ρ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ Λ : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ C : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => Λ p.1 p.2) ∧
      IsCompact C ∧ C ⊆ U ∧ (∀ y, ψ 0 y=y) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < Λ t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (a (ψ t y)) (fderiv ℝ (ψ t) y v)=Λ t y*B (a y) v) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, ψ t x=g t x := by sorry
