-- Prove2me | solution 1 for mme_CW_q6_uniform_isolated_address_set_to_hash_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:11:33.185631+00:00
-- url     : https://prove2.me/submissions/f521c627-d675-4471-a361-71cbb5341544

import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

/-- An isolated, uniformly fibered finite address set whose retained modes
are closed inside an ambient bucket canonically enumerates to a primary hash
family. -/
theorem solution
    (N L G H : ℕ)
    (E F : Finset (CWQ6ExactCoupledAddress N L G))
    (hH : 0 < H)
    (hFE : F ⊆ E)
    (hisolated : ∀ e ∈ F, ∀ e' ∈ E,
      (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e')
    (huniform : ∀ c ∈ F.image (fun e => e.1 2),
      (F.filter (fun e => e.1 2 = c)).card = H)
    (hclosed : ∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
      ∃ e' ∈ E,
        e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2) :
    Nonempty (CWQ6PrimaryHashFamily N L G
      (F.image (fun e => e.1 2)).card H) := by
  classical
  let Zs : Finset (Fin (2 * N) → Fin 3) := F.image (fun e => e.1 2)
  let zEnum : Fin Zs.card ≃ ↥Zs := Zs.equivFin.symm
  let fiber (a : Fin Zs.card) : Finset (CWQ6ExactCoupledAddress N L G) :=
    F.filter (fun e => e.1 2 = (zEnum a).1)
  have hfiberCard (a : Fin Zs.card) : (fiber a).card = H := by
    apply huniform
    exact (zEnum a).2
  let edgeEnum (a : Fin Zs.card) : Fin H ≃ ↥(fiber a) :=
    (Finset.equivFinOfCardEq (hfiberCard a)).symm
  let entry (p : Fin Zs.card × Fin H) :
      CWQ6ExactCoupledAddress N L G :=
    (edgeEnum p.1 p.2).1
  have hentryF (p : Fin Zs.card × Fin H) : entry p ∈ F := by
    exact (Finset.mem_filter.mp (edgeEnum p.1 p.2).2).1
  have hentryZ (p : Fin Zs.card × Fin H) :
      (entry p).1 2 = (zEnum p.1).1 := by
    exact (Finset.mem_filter.mp (edgeEnum p.1 p.2).2).2
  have hxInjective : Function.Injective (fun p => (entry p).1 0) := by
    rintro ⟨a, h⟩ ⟨b, k⟩ hxy
    have heq : entry (a, h) = entry (b, k) :=
      hisolated (entry (a, h)) (hentryF (a, h))
        (entry (b, k)) (hFE (hentryF (b, k))) (Or.inl hxy)
    have hab : a = b := by
      apply zEnum.injective
      apply Subtype.ext
      rw [← hentryZ (a, h), ← hentryZ (b, k), heq]
    subst b
    have hhk : h = k := by
      apply (edgeEnum a).injective
      apply Subtype.ext
      exact heq
    subst k
    rfl
  have hyInjective : Function.Injective (fun p => (entry p).1 1) := by
    rintro ⟨a, h⟩ ⟨b, k⟩ hxy
    have heq : entry (a, h) = entry (b, k) :=
      hisolated (entry (a, h)) (hentryF (a, h))
        (entry (b, k)) (hFE (hentryF (b, k))) (Or.inr hxy)
    have hab : a = b := by
      apply zEnum.injective
      apply Subtype.ext
      rw [← hentryZ (a, h), ← hentryZ (b, k), heq]
    subst b
    have hhk : h = k := by
      apply (edgeEnum a).injective
      apply Subtype.ext
      exact heq
    subst k
    rfl
  have hzSame : ∀ (a : Fin Zs.card) (h k : Fin H),
      (entry (a, h)).1 2 = (entry (a, k)).1 2 := by
    intro a h k
    rw [hentryZ (a, h), hentryZ (a, k)]
  have hzSeparate : ∀ (a b : Fin Zs.card) (h k : Fin H),
      (entry (a, h)).1 2 = (entry (b, k)).1 2 → a = b := by
    intro a b h k hz
    apply zEnum.injective
    apply Subtype.ext
    rw [← hentryZ (a, h), ← hentryZ (b, k), hz]
  have hinduced : ∀ p q r : Fin Zs.card × Fin H,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress (entry p).1 (entry q).1 (entry r).1) →
      p = q ∧ p.1 = r.1 := by
    intro p q r hsupp
    obtain ⟨e', he'E, hex, hey, hez⟩ :=
      hclosed (entry p) (hentryF p) (entry q) (hentryF q)
        (entry r) (hentryF r) hsupp
    have hp : entry p = e' :=
      hisolated (entry p) (hentryF p) e' he'E (Or.inl hex.symm)
    have hq : entry q = e' :=
      hisolated (entry q) (hentryF q) e' he'E (Or.inr hey.symm)
    have hpq : p = q := by
      apply hxInjective
      change (entry p).1 0 = (entry q).1 0
      rw [hp, hq]
    refine ⟨hpq, ?_⟩
    exact hzSeparate p.1 r.1 p.2 r.2 (by
      rw [hp, hez])
  exact ⟨{
    hHpos := hH
    entry := entry
    xInjective := hxInjective
    yInjective := hyInjective
    zSameFiber := hzSame
    zSeparatesFibers := hzSeparate
    induced := hinduced
  }⟩
