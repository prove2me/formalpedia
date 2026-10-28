-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_depolarizing_choi
-- name    : CerfCloning.Isotropic.depolarizing_choi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:42.856337+00:00
-- url     : https://prove2.me/theorems/c524fa21-ab4a-4f67-a9cd-712dd7fd986d
-- title:
--   §III C, p. 15, after (3.18) — a channel is depolarizing with fraction $\pi$ iff its joint state with $R$ is $(1-\pi)|\psi_{0,0}\rangle\langle\psi_{0,0}| + \pi\,\mathbb 1\otimes\mathbb 1/N^2$
-- statement:
--   Let $N \ge 1$ and $\pi \in \mathbb R$, and let $\mathcal D_\pi(\rho) = \frac{\pi}{N}(\operatorname{Tr}\rho)\,\mathbb 1 + (1-\pi)\,\rho$ be the $N$-dimensional depolarizing channel with depolarizing fraction $\pi$: the input state is replaced by the random state $\mathbb 1/N$ with probability $\pi$ and left unchanged with probability $1-\pi$. If its input is maximally entangled with a reference $R$, the joint output state is
--   $$(\mathrm{id}_R \otimes \mathcal D_\pi)\big(|\psi_{0,0}\rangle\langle\psi_{0,0}|\big) = (1-\pi)\,|\psi_{0,0}\rangle\langle\psi_{0,0}| + \pi\,\frac{\mathbb 1 \otimes \mathbb 1}{N^2} .$$
--   Conversely, every quantum channel $\Phi$ on the $N$-level system whose joint state with $R$ is this state, $(\mathrm{id}_R \otimes \Phi)(|\psi_{0,0}\rangle\langle\psi_{0,0}|) = (1-\pi)\,|\psi_{0,0}\rangle\langle\psi_{0,0}| + \pi\,\mathbb 1 \otimes \mathbb 1/N^2$, is the depolarizing channel $\mathcal D_\pi$.
--
--   Comparing with Eq. (3.18) under the normalization (3.17), whose first coefficient is then $1 - |a|^2$, identifies output $A$ of the isotropic Heisenberg cloner as the depolarizing channel with fraction $\pi_a = |a|^2$ ($a = 0$: perfect channel; $a = 1$: fully depolarizing channel). This is the meaning of the depolarizing fractions in the no-cloning inequality.
--
--   **Formalization Note** $\mathcal D_\pi$ is the published `QAlgorithms.QuditFidelity.depolarizingMap`, and $\mathrm{id}_R \otimes \mathcal D_\pi$ is `QAlgorithms.idTensorSuperop` with $R$ the first factor.
--
--   Differences from the source:
--   - reading: "so that the input state is replaced by a random state with probability $\pi_a = |a|^2$" (the channel whose joint state with $R$ is (3.18) is depolarizing with fraction $|a|^2$) → a channel has joint state $(1-\pi)|\psi_{0,0}\rangle\langle\psi_{0,0}| + \pi\,\mathbb 1\otimes\mathbb 1/N^2$ with $R$ if and only if it is the depolarizing channel with fraction $\pi$ (both directions stated); reason: the sentence identifies the channel from its joint state, with $\pi = |a|^2$ once (3.17) makes the first coefficient of (3.18) equal to $1 - |a|^2$.
--   - generalization: $\pi_a = |a|^2 \in [0,1]$ → any real $\pi$; reason: both directions hold for every real $\pi$, and $\pi = |a|^2$ is an instance.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, p. 15, sentence after Eq. (3.18), 'so that the input state is replaced by a random state with probability πa = |a|² …'

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem depolarizing_choi (N : ℕ) [NeZero N] (pa : ℝ) :
    idTensorSuperop (R := Fin N) (QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) pa)
        (pureDensity (meState N 0 0)) =
      ((1 - pa : ℝ) : ℂ) • pureDensity (meState N 0 0) + ((pa / (N : ℝ) ^ 2 : ℝ) : ℂ) • 1 ∧
    ∀ Φ : Superop (Fin N) (Fin N), IsChannel Φ →
      idTensorSuperop (R := Fin N) Φ (pureDensity (meState N 0 0)) =
        ((1 - pa : ℝ) : ℂ) • pureDensity (meState N 0 0) + ((pa / (N : ℝ) ^ 2 : ℝ) : ℂ) • 1 →
      Φ = QuditFidelity.depolarizingMap N (Nat.pos_of_neZero N) pa := by sorry
end CerfCloning.Isotropic
